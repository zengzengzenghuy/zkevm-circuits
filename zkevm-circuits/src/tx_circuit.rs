// TODO Remove th gadgetis
#![allow(missing_docs)]
// TODO Remove this
#![allow(unused_imports)]

use crate::gadget::is_zero::{IsZeroChip, IsZeroConfig, IsZeroInstruction};
use ecc::{EccConfig, GeneralEccChip};
use ecdsa::ecdsa::{AssignedEcdsaSig, AssignedPublicKey, EcdsaChip, EcdsaConfig};
use group::{ff::Field, prime::PrimeCurveAffine, Curve};
use halo2_proofs::{
    arithmetic::{BaseExt, CurveAffine},
    circuit::{AssignedCell, Layouter, Region, SimpleFloorPlanner},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector,
        VirtualCells,
    },
    poly::Rotation,
};
use integer::{
    AssignedInteger, IntegerChip, IntegerConfig, IntegerInstructions, WrongExt,
    NUMBER_OF_LOOKUP_LIMBS,
};
use keccak256::plain::Keccak;
use maingate::{
    Assigned, AssignedCondition, MainGate, MainGateConfig, RangeChip, RangeConfig,
    RangeInstructions, RegionCtx,
};
use pairing::arithmetic::FieldExt;
use secp256k1::Secp256k1Affine;
use std::cmp::min;
use std::convert::TryInto;
use std::{io::Cursor, marker::PhantomData, os::unix::prelude::FileTypeExt};

// TODO: Move these utils outside of `evm_circuit` so that they can be used by
// other circuits without crossing boundaries.
use crate::evm_circuit::util::{and, not, or, select, RandomLinearCombination, Word};
use crate::util::Expr;

const POW_RAND_SIZE: usize = 63;

/// Auxiliary Gadget to verify a that a message hash is signed by the public
/// key corresponding to an Ethereum Address.
#[derive(Default, Debug)]
struct SignVerifyChip<F: FieldExt, const MAX_VERIF: usize> {
    aux_generator: Secp256k1Affine,
    window_size: usize,
    _marker: PhantomData<F>,
    // ecdsa_chip: EcdsaChip<Secp256k1Affine, F>,
}

const KECCAK_IS_ENABLED: usize = 0;
const KECCAK_INPUT_RLC: usize = 1;
const KECCAK_INPUT_LEN: usize = 2;
const KECCAK_OUTPUT_RLC: usize = 3;

const BIT_LEN_LIMB: usize = 72;

/// Return an expression that builds an integer element in the field from the
/// `bytes` in little endian.
fn int_from_bytes_le<'a, F: FieldExt>(
    bytes: impl IntoIterator<Item = &'a Expression<F>>,
) -> Expression<F> {
    // sum_{i = 0}^{N} bytes[i] * 256^i
    let mut res = 0u8.expr();
    for (i, byte) in bytes.into_iter().enumerate() {
        res = res + byte.clone() * Expression::Constant(F::from(256).pow(&[i as u64, 0, 0, 0]))
    }
    res
}

/// Return a list of expression that evaluate to 0 when the `bytes` are a little
/// endian representation of the integer split into `limbs`.  Assumes `limbs`
/// are 72 bits (9 bytes).
fn integer_eq_bytes_le<F: FieldExt>(
    limbs: &[Expression<F>; 4],
    bytes: &[Expression<F>; 32],
) -> Vec<Expression<F>> {
    let mut res = Vec::new();
    for (j, limb) in limbs.iter().enumerate() {
        let limb_bytes = &bytes[j * 9..min((j + 1) * 9, bytes.len())];
        let limb_exp = int_from_bytes_le(limb_bytes);
        res.push(limb.clone() - limb_exp);
    }
    res
}

/// Enable copy constraint between `src` integer limbs and `dst` limbs.  Then
/// assign the `dst` limbs values from `src`.
fn copy_integer<F: FieldExt, W: WrongExt>(
    region: &mut Region<'_, F>,
    name: &str,
    src: AssignedInteger<W, F>,
    dst: &[Column<Advice>; 4],
    offset: usize,
) -> Result<(), Error> {
    for (i, limb) in src.limbs().iter().enumerate() {
        let assigned_cell = region.assign_advice(
            || format!("{} limb {}", name, i),
            dst[i],
            offset,
            || limb.value().clone().ok_or(Error::Synthesis),
        )?;
        region.constrain_equal(assigned_cell.cell(), limb.cell())?;
    }
    Ok(())
}

fn assign_integer_bytes_le<F: FieldExt, W: BaseExt>(
    region: &mut Region<'_, F>,
    name: &str,
    src: W,
    dst: &[Column<Advice>],
    offset: usize,
) -> Result<(), Error> {
    let mut src_le = [0u8; 32];
    src.write(&mut Cursor::new(&mut src_le[..])).unwrap();
    for (i, byte) in src_le.iter().enumerate() {
        region.assign_advice(
            || format!("{} byte {}", name, i),
            dst[i],
            offset,
            || Ok(F::from(*byte as u64)),
        )?;
    }
    Ok(())
}

#[derive(Debug, Clone)]
struct SignVerifyConfig<F: FieldExt> {
    q_enable: Selector,
    pk_hash: [Column<Advice>; 32],
    address: Column<Advice>,
    address_is_zero: IsZeroConfig<F>,
    address_inv: Column<Advice>,
    msg_hash_rlc: Column<Advice>,
    // msg_hash_rlc_is_zero: IsZeroConfig<F>,
    // msg_hash_rlc_inv: Column<Advice>,

    // ECDSA
    main_gate_config: MainGateConfig,
    range_config: RangeConfig,
    // First 32 cells are coord x in little endian, following 32 cells are coord y in little
    // endian.
    pk: [Column<Advice>; 32 * 2],
    pk_x_limbs: [Column<Advice>; 4],
    pk_y_limbs: [Column<Advice>; 4],
    msg_hash: [Column<Advice>; 32],
    msg_hash_limbs: [Column<Advice>; 4],
    ecdsa_result: Column<Advice>,
    // signature: [[Column<Advice>; 32]; 2],
    power_of_randomness: [Column<Instance>; POW_RAND_SIZE],

    // [is_enabled, input_rlc, input_len, output_rlc]
    keccak_table: [Column<Advice>; 4],
}

impl<F: FieldExt> SignVerifyConfig<F> {
    pub fn new(
        meta: &mut ConstraintSystem<F>,
        power_of_randomness: [Column<Instance>; POW_RAND_SIZE],
    ) -> Self {
        let q_enable = meta.complex_selector();

        let pk = [(); 32 * 2].map(|_| meta.advice_column());
        let pk_x_limbs = [(); 4].map(|_| meta.advice_column());
        pk_x_limbs.map(|c| meta.enable_equality(c));
        let pk_y_limbs = [(); 4].map(|_| meta.advice_column());
        pk_y_limbs.map(|c| meta.enable_equality(c));
        let msg_hash = [(); 32].map(|_| meta.advice_column());
        let msg_hash_limbs = [(); 4].map(|_| meta.advice_column());
        msg_hash_limbs.map(|c| meta.enable_equality(c));
        let ecdsa_result = meta.advice_column();
        meta.enable_equality(ecdsa_result);

        // create address, msg_hash, pk_hash, and msg_hash_inv, and iz_zero

        let address = meta.advice_column();
        let pk_hash = [(); 32].map(|_| meta.advice_column());

        let msg_hash_rlc = meta.advice_column();

        // is_enabled === msg_hash_rlc != 0

        let address_inv = meta.advice_column();
        let address_is_zero = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(q_enable),
            |meta| meta.query_advice(address, Rotation::cur()),
            address_inv,
        );
        let is_not_padding = not::expr(address_is_zero.is_zero_expression.clone());

        // lookup keccak table

        let keccak_table = [(); 4].map(|_| meta.advice_column());
        // let pow_rand_cols = [(); POW_RAND_SIZE].map(|_| meta.instance_column());

        let mut power_of_randomness_exp = None;
        meta.create_gate("", |meta| {
            power_of_randomness_exp = Some(
                power_of_randomness.map(|column| meta.query_instance(column, Rotation::cur())),
            );
            [0u8.expr()]
        });
        let power_of_randomness_exp = power_of_randomness_exp.unwrap();

        // keccak lookup
        meta.lookup_any("keccak", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let selector = q_enable * is_not_padding.clone();
            let mut table_map = Vec::new();

            // Column 0: is_enabled
            let keccak_is_enabled =
                meta.query_advice(keccak_table[KECCAK_IS_ENABLED], Rotation::cur());
            table_map.push((selector.clone(), keccak_is_enabled));

            // Column 1: input_rlc (pk_rlc)
            let keccak_input_rlc =
                meta.query_advice(keccak_table[KECCAK_INPUT_RLC], Rotation::cur());
            let mut pk_be = pk.map(|c| meta.query_advice(c, Rotation::cur()));
            pk_be[..32].reverse();
            pk_be[32..].reverse();
            let pk_rlc = RandomLinearCombination::random_linear_combine_expr(
                pk_be,
                &power_of_randomness_exp,
            );
            // DBG
            // let pk_rlc = power_of_randomness[..31]
            //     .iter()
            //     .fold(0.expr(), |acc, val| acc * 256.expr() + val.clone());
            table_map.push((selector.clone() * pk_rlc, keccak_input_rlc));

            // Column 2: input_len (64)
            let keccak_input_len =
                meta.query_advice(keccak_table[KECCAK_INPUT_LEN], Rotation::cur());
            table_map.push((selector.clone() * 64usize.expr(), keccak_input_len));

            // Column 3: output_rlc (pk_hash_rlc)
            let keccak_output_rlc =
                meta.query_advice(keccak_table[KECCAK_OUTPUT_RLC], Rotation::cur());
            let pk_hash = pk_hash.map(|c| meta.query_advice(c, Rotation::cur()));
            let pk_hash_rlc = RandomLinearCombination::random_linear_combine_expr(
                pk_hash,
                &power_of_randomness_exp,
            );
            table_map.push((selector.clone() * pk_hash_rlc, keccak_output_rlc));

            table_map
        });

        meta.create_gate("when not_padding, ecdsa_result = true", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let ecdsa_result = meta.query_advice(ecdsa_result, Rotation::cur());
            vec![q_enable * (is_not_padding.clone() - ecdsa_result)]
        });

        meta.create_gate("address is is_not_padding * pk_hash[-20:]", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let pk_hash = pk_hash.map(|c| meta.query_advice(c, Rotation::cur()));
            let address = meta.query_advice(address, Rotation::cur());

            let addr_from_pk = int_from_bytes_le(pk_hash[32 - 20..].iter().rev());

            vec![q_enable * (address - is_not_padding.clone() * addr_from_pk)]
        });

        meta.create_gate("msg_hash in ECDSA equal their bytes", |meta| -> Vec<_> {
            let q_enable = meta.query_selector(q_enable);
            let msg_hash = msg_hash.map(|c| meta.query_advice(c, Rotation::cur()));
            let msg_hash_limbs = msg_hash_limbs.map(|c| meta.query_advice(c, Rotation::cur()));

            integer_eq_bytes_le(&msg_hash_limbs, &msg_hash)
                .into_iter()
                .map(|c| q_enable.clone() * c)
                .collect()
        });
        meta.create_gate("pk x in ECDSA equal their bytes", |meta| -> Vec<_> {
            let q_enable = meta.query_selector(q_enable);
            let pk_x: [Column<Advice>; 32] = pk[..32].try_into().unwrap();
            let pk_x = pk_x.map(|c| meta.query_advice(c.clone(), Rotation::cur()));
            let pk_x_limbs = pk_x_limbs.map(|c| meta.query_advice(c, Rotation::cur()));

            integer_eq_bytes_le(&pk_x_limbs, &pk_x)
                .into_iter()
                .map(|c| q_enable.clone() * c)
                .collect()
        });
        meta.create_gate("pk y in ECDSA equal their bytes", |meta| -> Vec<_> {
            let q_enable = meta.query_selector(q_enable);
            let pk_y: [Column<Advice>; 32] = pk[32..].try_into().unwrap();
            let pk_y = pk_y.map(|c| meta.query_advice(c.clone(), Rotation::cur()));
            let pk_y_limbs = pk_y_limbs.map(|c| meta.query_advice(c, Rotation::cur()));

            integer_eq_bytes_le(&pk_y_limbs, &pk_y)
                .into_iter()
                .map(|c| q_enable.clone() * c)
                .collect()
        });

        meta.create_gate("msg_hash_rlc = is_not_padding * RLC(msg_hash)", |meta| {
            let q_enable = meta.query_selector(q_enable);
            let msg_hash = msg_hash.map(|c| meta.query_advice(c, Rotation::cur()));
            let msg_hash_rlc = meta.query_advice(msg_hash_rlc, Rotation::cur());

            let expected_msg_hash_rlc = RandomLinearCombination::random_linear_combine_expr(
                msg_hash,
                &power_of_randomness_exp[..32],
            );
            vec![q_enable * (msg_hash_rlc - is_not_padding.clone() * expected_msg_hash_rlc)]
        });

        // ECDSA config
        let (rns_base, rns_scalar) = GeneralEccChip::<Secp256k1Affine, F>::rns(BIT_LEN_LIMB);
        let main_gate_config = MainGate::<F>::configure(meta);
        let mut overflow_bit_lengths: Vec<usize> = vec![];
        overflow_bit_lengths.extend(rns_base.overflow_lengths());
        overflow_bit_lengths.extend(rns_scalar.overflow_lengths());
        let range_config = RangeChip::<F>::configure(meta, &main_gate_config, overflow_bit_lengths);

        Self {
            q_enable,
            pk_hash,
            address,
            msg_hash_rlc,
            address_is_zero,
            address_inv,
            range_config,
            main_gate_config,
            pk,
            pk_x_limbs,
            pk_y_limbs,
            msg_hash,
            msg_hash_limbs,
            ecdsa_result,
            power_of_randomness,
            keccak_table,
        }
    }
}

struct KeccakAux {
    input: [u8; 64],
    output: [u8; 32],
}

impl<F: FieldExt> SignVerifyConfig<F> {
    pub fn load_range(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        let bit_len_lookup = BIT_LEN_LIMB / NUMBER_OF_LOOKUP_LIMBS;
        let range_chip = RangeChip::<F>::new(self.range_config.clone(), bit_len_lookup);
        range_chip.load_limb_range_table(layouter)?;
        range_chip.load_overflow_range_tables(layouter)?;

        Ok(())
    }

    fn keccak_assign_row(
        &self,
        region: &mut Region<'_, F>,
        offset: usize,
        is_enabled: F,
        input_rlc: F,
        input_len: usize,
        output_rlc: F,
    ) -> Result<(), Error> {
        for (name, column, value) in &[
            ("is_enabled", self.keccak_table[0], is_enabled),
            ("input_rlc", self.keccak_table[1], input_rlc),
            ("input_len", self.keccak_table[2], F::from(input_len as u64)),
            ("output_rlc", self.keccak_table[3], output_rlc),
        ] {
            region.assign_advice(
                || format!("Keccak table assign {} {}", name, offset),
                *column,
                offset,
                || Ok(*value),
            )?;
        }
        Ok(())
    }

    pub fn load_keccak(
        &self,
        layouter: &mut impl Layouter<F>,
        auxs: Vec<KeccakAux>,
        randomness: F,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "keccak table",
            |mut region| {
                let mut offset = 0;

                // All zero row to allow simulating a disabled lookup.
                self.keccak_assign_row(&mut region, offset, F::zero(), F::zero(), 0, F::zero())?;
                offset += 1;

                for aux in &auxs {
                    let KeccakAux { input, output } = aux;
                    let input_rlc =
                        RandomLinearCombination::random_linear_combine(input.clone(), randomness);
                    let output_rlc = Word::random_linear_combine(output.clone(), randomness);
                    // println!(
                    //     "DBG keccak [{:?}, {:}, {:?}]",
                    //     input_rlc,
                    //     input.len(),
                    //     output_rlc
                    // );
                    self.keccak_assign_row(
                        &mut region,
                        offset,
                        F::one(),
                        input_rlc,
                        input.len(),
                        output_rlc,
                    )?;
                    offset += 1;
                }
                Ok(())
            },
        )?;
        Ok(())
    }

    pub fn ecc_chip_config(&self) -> EccConfig {
        EccConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }

    pub fn integer_chip_config(&self) -> IntegerConfig {
        IntegerConfig::new(self.range_config.clone(), self.main_gate_config.clone())
    }
}

pub struct AssignedECDSA<F: FieldExt> {
    pk_x: AssignedInteger<secp256k1::Fp, F>,
    pk_y: AssignedInteger<secp256k1::Fp, F>,
    msg_hash: AssignedInteger<secp256k1::Fq, F>,
    result: AssignedCondition<F>,
}

pub struct AssignedSignatureVerify<F: FieldExt> {
    address: AssignedCell<F, F>,
    msg_hash_rlc: AssignedCell<F, F>,
}

impl<F: FieldExt, const MAX_VERIF: usize> SignVerifyChip<F, MAX_VERIF> {
    pub fn assign_aux(
        &self,
        region: &mut Region<'_, F>,
        ecc_chip: &mut GeneralEccChip<Secp256k1Affine, F>,
    ) -> Result<(), Error> {
        let ctx_offset = &mut 0;
        let ctx = &mut RegionCtx::new(region, ctx_offset);

        ecc_chip.assign_aux_generator(ctx, Some(self.aux_generator))?;
        ecc_chip.assign_aux(ctx, self.window_size, 1)?;
        println!("DBG ctx_offset = {}", *ctx_offset);
        Ok(())
    }

    pub fn assign_ecdsa(
        &self,
        ctx: &mut RegionCtx<F>,
        ecc_chip: &mut GeneralEccChip<Secp256k1Affine, F>,
        scalar_chip: &IntegerChip<secp256k1::Fq, F>,
        ecdsa_chip: &EcdsaChip<Secp256k1Affine, F>,
        tx: &TxSignData,
    ) -> Result<AssignedECDSA<F>, Error> {
        let TxSignData {
            signature,
            pk,
            msg_hash,
        } = tx;
        let (sig_r, sig_s) = signature;

        // let ctx_offset = &mut 0;
        // let ctx = &mut RegionCtx::new(region, ctx_offset);

        let integer_r = ecc_chip.new_unassigned_scalar(Some(*sig_r));
        let integer_s = ecc_chip.new_unassigned_scalar(Some(*sig_s));
        let msg_hash = ecc_chip.new_unassigned_scalar(Some(*msg_hash));

        let r_assigned = scalar_chip.assign_integer(ctx, integer_r)?;
        let s_assigned = scalar_chip.assign_integer(ctx, integer_s)?;
        let sig = AssignedEcdsaSig {
            r: r_assigned,
            s: s_assigned,
        };

        let pk_in_circuit = ecc_chip.assign_point(ctx, Some((*pk).into()))?;
        let pk_assigned = AssignedPublicKey {
            point: pk_in_circuit,
        };
        let msg_hash = scalar_chip.assign_integer(ctx, msg_hash)?;
        let result = ecdsa_chip.verify(ctx, &sig, &pk_assigned, &msg_hash)?;

        // Copy constraint between ecdsa verification integers and local columns
        // copy_integer(&mut region, "sig_r", sig.r, &config.sig_r_limbs, offset)?;
        // copy_integer(&mut region, "sig_s", sig.s, &config.sig_s_limbs, offset)?;

        Ok(AssignedECDSA {
            pk_x: pk_assigned.point.get_x(),
            pk_y: pk_assigned.point.get_y(),
            msg_hash,
            result,
        })
    }

    pub fn assign_signature_verify(
        &self,
        config: &SignVerifyConfig<F>,
        region: &mut Region<'_, F>,
        offset: usize,
        address_is_zero_chip: &IsZeroChip<F>,
        randomness: F,
        tx: &TxSignData,
        assigned_ecdsa: &AssignedECDSA<F>,
    ) -> Result<(AssignedSignatureVerify<F>, KeccakAux), Error> {
        let TxSignData {
            signature: _,
            pk,
            msg_hash,
        } = tx;

        copy_integer(
            region,
            "pk_x",
            assigned_ecdsa.pk_x.clone(),
            &config.pk_x_limbs,
            offset,
        )?;
        copy_integer(
            region,
            "pk_y",
            assigned_ecdsa.pk_y.clone(),
            &config.pk_y_limbs,
            offset,
        )?;
        copy_integer(
            region,
            "msg_hash",
            assigned_ecdsa.msg_hash.clone(),
            &config.msg_hash_limbs,
            offset,
        )?;
        let ecdsa_result_assigned = region.assign_advice(
            || format!("ECDSA verify result"),
            config.ecdsa_result,
            offset,
            || assigned_ecdsa.result.value().ok_or(Error::Synthesis),
        )?;
        region.constrain_equal(ecdsa_result_assigned.cell(), assigned_ecdsa.result.cell())?;

        config.q_enable.enable(region, offset)?;

        // Assign msg_hash_rlc
        let mut msg_hash_le = [0u8; 32];
        msg_hash
            .write(&mut Cursor::new(&mut msg_hash_le[..]))
            .unwrap();
        let msg_hash_rlc = Word::random_linear_combine(msg_hash_le, randomness);
        let msg_hash_rlc_assigned = region.assign_advice(
            || format!("msg_hash_rlc"),
            config.msg_hash_rlc,
            offset,
            || Ok(msg_hash_rlc),
        )?;

        // Assign pk
        let pk_coord = pk.coordinates().unwrap();
        let mut pk_x_le = [0u8; 32];
        let mut pk_y_le = [0u8; 32];
        pk_coord
            .x()
            .write(&mut Cursor::new(&mut pk_x_le[..]))
            .unwrap();
        pk_coord
            .y()
            .write(&mut Cursor::new(&mut pk_y_le[..]))
            .unwrap();
        for (i, byte) in pk_x_le.iter().enumerate() {
            // println!("DBG pk x {:02} = {:02x}", i, byte);
            region.assign_advice(
                || format!("pk x byte {}", i),
                config.pk[i],
                offset,
                || Ok(F::from(*byte as u64)),
            )?;
        }
        for (i, byte) in pk_y_le.iter().enumerate() {
            // println!("DBG pk y {:02} = {:02x}", i, byte);
            region.assign_advice(
                || format!("pk y byte {}", i),
                config.pk[32 + i],
                offset,
                || Ok(F::from(*byte as u64)),
            )?;
        }

        let mut pk_x_be = pk_x_le.clone();
        pk_x_be.reverse();
        let mut pk_y_be = pk_y_le.clone();
        pk_y_be.reverse();
        let mut pk_bytes_be = [0u8; 64];
        pk_bytes_be[..32].copy_from_slice(&pk_x_be);
        pk_bytes_be[32..].copy_from_slice(&pk_y_be);
        let pk_hash = if *msg_hash == secp256k1::Fq::one() {
            vec![0u8; 32] // Enable padding with address = 0
        } else {
            let mut keccak = Keccak::default();
            keccak.update(&pk_bytes_be);
            keccak.digest()
        };
        println!("DBG pk_hash: {:x?}", pk_hash);
        let address = pub_key_hash_to_address(&pk_hash);
        println!("DBG address: {:?}", address);

        // Assign pk_hash
        for (i, byte) in pk_hash.iter().enumerate() {
            region.assign_advice(
                || format!("pk_hash byte {}", i),
                config.pk_hash[i],
                offset,
                || Ok(F::from(*byte as u64)),
            )?;
        }

        // Assign address and address_is_zero_chip
        let address_assigned = region.assign_advice(
            || format!("address"),
            config.address,
            offset,
            || Ok(address),
        )?;
        address_is_zero_chip.assign(region, offset, Some(address))?;

        // Assign msg_hash
        for (i, byte) in msg_hash_le.iter().enumerate() {
            region.assign_advice(
                || format!("msg_hash byte {}", i),
                config.msg_hash[i],
                offset,
                || Ok(F::from(*byte as u64)),
            )?;
        }

        Ok((
            AssignedSignatureVerify {
                address: address_assigned,
                msg_hash_rlc: msg_hash_rlc_assigned,
            },
            KeccakAux {
                input: pk_bytes_be,
                output: pk_hash.try_into().unwrap(),
            },
        ))
    }

    pub fn assign_txs(
        &self,
        config: &SignVerifyConfig<F>,
        layouter: &mut impl Layouter<F>,
        randomness: F,
        txs: &[TxSignData],
    ) -> Result<(), Error> {
        if txs.len() > MAX_VERIF {
            panic!("txs.len() = {} > MAX_VERIF = {}", txs.len(), MAX_VERIF);
        }
        let mut ecc_chip =
            GeneralEccChip::<Secp256k1Affine, F>::new(config.ecc_chip_config(), BIT_LEN_LIMB);
        let scalar_chip = ecc_chip.scalar_field_chip();

        // NOTE: moving the assign region of the "aux" after the "signature verify +
        // ecdsa chip verification" causes a `Synthesis` error.
        layouter.assign_region(
            || "ecc chip aux",
            |mut region| self.assign_aux(&mut region, &mut ecc_chip),
        )?;

        let ecdsa_chip = EcdsaChip::new(ecc_chip.clone());
        let address_is_zero_chip = IsZeroChip::construct(config.address_is_zero.clone());

        let mut assigned_ecdsas = Vec::new();
        let mut keccak_auxs = Vec::new();

        layouter.assign_region(
            || "ecdsa chip verification",
            |mut region| {
                let offset = &mut 0;
                let mut ctx = RegionCtx::new(&mut region, offset);
                for i in 0..MAX_VERIF {
                    let tx = if i < txs.len() {
                        txs[i].clone()
                    } else {
                        // pading (enabled when msg_hash == 0)
                        TxSignData::default()
                    };
                    let assigned_ecdsa =
                        self.assign_ecdsa(&mut ctx, &mut ecc_chip, &scalar_chip, &ecdsa_chip, &tx)?;
                    assigned_ecdsas.push(assigned_ecdsa);
                }
                println!("DBG ctx_offset = {}", *offset);
                Ok(())
            },
        )?;

        layouter.assign_region(
            || "signature address verify",
            |mut region| {
                let mut offset = 0;
                for i in 0..MAX_VERIF {
                    let tx = if i < txs.len() {
                        txs[i].clone()
                    } else {
                        // pading (enabled when msg_hash == 0)
                        TxSignData::default()
                    };
                    let assigned_ecdsa = &assigned_ecdsas[i];
                    let (_, keccak_aux) = self.assign_signature_verify(
                        &config,
                        &mut region,
                        offset,
                        &address_is_zero_chip,
                        randomness,
                        &tx,
                        assigned_ecdsa,
                    )?;
                    offset += 1;
                    if i < txs.len() {
                        keccak_auxs.push(keccak_aux);
                    }
                }

                Ok(())
            },
        )?;

        config.load_keccak(layouter, keccak_auxs, randomness)?;
        config.load_range(layouter)?;

        Ok(())
    }

    /*
    pub fn assign_tx(
        mut layouter: impl Layouter<F>,
        config: Self::Config,
        randomness: F,
        tx: &TxSignData,
    ) -> Result<(), Error> {
        Ok(())
    }
    */

    /*
        pub fn load_tables(config: &SignVerifyConfig<F>, layouter: &mut impl Layouter<F>) {
            use ecdsa::maingate::RangeInstructions;
            const BIT_LEN_LIMB: usize = 68;
            use ecdsa::integer::NUMBER_OF_LOOKUP_LIMBS;

            let bit_len_lookup = BIT_LEN_LIMB / NUMBER_OF_LOOKUP_LIMBS;
            let range_chip = RangeChip::<F>::new(config.range_config.clone(), bit_len_lookup).unwrap();
            range_chip.load_limb_range_table(layouter).unwrap();
            range_chip.load_overflow_range_tables(layouter).unwrap();
       }
    */
}

#[derive(Clone, Debug)]
struct TxSignData {
    signature: (secp256k1::Fq, secp256k1::Fq),
    pk: Secp256k1Affine,
    msg_hash: secp256k1::Fq,
}

impl Default for TxSignData {
    fn default() -> Self {
        Self {
            // Hardcoded signature (r, s) values that make the ECDSA chip pass the constraints, to
            // use for the case where we don't want to do the verification in a padding
            // verification.
            signature: (
                secp256k1::Fq::from_raw([
                    0x21a1e47cdca2154d,
                    0x2df430adafa747ad,
                    0xa95cf188e4147bc5,
                    0xce4d6d14ce9b6c24,
                ]),
                secp256k1::Fq::from_raw([
                    0x3d18180571923957,
                    0x59a31324f3d31663,
                    0xb0650a05780d8b36,
                    0xd5a692e5f8f736ac,
                ]),
            ),
            pk: Secp256k1Affine::generator(),
            msg_hash: secp256k1::Fq::one(),
        }
    }
}

fn pub_key_hash_to_address<F: FieldExt>(pk_hash: &[u8]) -> F {
    pk_hash[32 - 20..]
        .iter()
        .fold(F::zero(), |acc, b| acc * F::from(256) + F::from(*b as u64))
}

/*
pub trait SignVerifyInstruction<F: FieldExt> {
    fn check(pk_hash: Vec<u8>, address: F, msg_hash_rlc: F, random: F) -> Result<(), Error>;
}
*/

#[cfg(test)]
mod sign_verify_tets {
    use super::*;
    use group::Group;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::pairing::bn256::Fr;
    use pretty_assertions::assert_eq;
    use rand::RngCore;
    use rand::SeedableRng;
    use rand_xorshift::XorShiftRng;

    #[derive(Clone, Debug)]
    struct TestCircuitSignVerifyConfig<F: FieldExt> {
        sign_verify: SignVerifyConfig<F>,
        /* main_gate_config: MainGateConfig,
         * range_config: RangeConfig,
         * // sig_s_limbs: [Column<Advice>; 4],
         * // sig_r_limbs: [Column<Advice>; 4],
         * pk_x_limbs: [Column<Advice>; 4],
         * pk_y_limbs: [Column<Advice>; 4],
         * msg_hash_limbs: [Column<Advice>; 4], */
    }

    impl<F: FieldExt> TestCircuitSignVerifyConfig<F> {
        pub fn new(meta: &mut ConstraintSystem<F>) -> Self {
            let power_of_randomness = {
                [(); POW_RAND_SIZE].map(|_| meta.instance_column())
                // let columns = [(); POW_RAND_SIZE].map(|_|
                // meta.instance_column());
                // let mut power_of_randomness = None;

                // meta.create_gate("power of randomness", |meta| {
                //     power_of_randomness =
                //         Some(columns.map(|column| meta.query_instance(column,
                // Rotation::cur())));

                //     [0.expr()]
                // });

                // power_of_randomness.unwrap()
            };

            let sign_verify = SignVerifyConfig::new(meta, power_of_randomness);
            TestCircuitSignVerifyConfig { sign_verify }
        }
    }

    #[derive(Default)]
    struct TestCircuitSignVerify<F: FieldExt, const MAX_VERIF: usize> {
        sign_verify: SignVerifyChip<F, MAX_VERIF>,
        randomness: F,
        // power_of_randomness: [Expression<F>; POW_RAND_SIZE],
        txs: Vec<TxSignData>,
    }

    impl<F: FieldExt, const MAX_VERIF: usize> Circuit<F> for TestCircuitSignVerify<F, MAX_VERIF> {
        type Config = TestCircuitSignVerifyConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            TestCircuitSignVerifyConfig::new(meta)
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            self.sign_verify.assign_txs(
                &config.sign_verify,
                &mut layouter,
                self.randomness,
                &self.txs,
            )?;
            // self.sign_verify.assign(
            //     &config.sign_verify,
            //     &mut layouter,
            //     self.randomness,
            //     self.txs[1].clone(),
            // )?;
            Ok(())
        }
    }

    const VERIF_HEIGHT: usize = 1;

    fn run<F: FieldExt, const MAX_VERIF: usize>(txs: Vec<TxSignData>) {
        let k = 20;
        let mut rng = XorShiftRng::seed_from_u64(2);
        let aux_generator =
            <Secp256k1Affine as CurveAffine>::CurveExt::random(&mut rng).to_affine();

        let randomness = F::random(&mut rng);
        let mut power_of_randomness: Vec<Vec<F>> = (1..POW_RAND_SIZE + 1)
            .map(|exp| vec![randomness.pow(&[exp as u64, 0, 0, 0]); txs.len() * VERIF_HEIGHT])
            .collect();
        // SignVerifyChip -> ECDSAChip -> MainGate instance column
        power_of_randomness.push(vec![]);
        // println!("DBG power_of_randomness: {:?}", power_of_randomness);
        let circuit = TestCircuitSignVerify::<F, MAX_VERIF> {
            sign_verify: SignVerifyChip {
                aux_generator,
                window_size: 2,
                _marker: PhantomData,
            },
            randomness,
            txs,
        };

        // let public_inputs = vec![vec![]];
        let prover = match MockProver::run(k, &circuit, power_of_randomness) {
            Ok(prover) => prover,
            Err(e) => panic!("{:#?}", e),
        };
        assert_eq!(prover.verify(), Ok(()));
    }

    // Generate a test key pair
    fn gen_key_pair(rng: impl RngCore) -> (secp256k1::Fq, Secp256k1Affine) {
        // generate a valid signature
        let generator = <Secp256k1Affine as PrimeCurveAffine>::generator();
        let sk = <Secp256k1Affine as CurveAffine>::ScalarExt::random(rng);
        let pk = generator * sk;
        let pk = pk.to_affine();

        (sk, pk)
    }

    // Generate a test message hash
    fn gen_msg_hash(rng: impl RngCore) -> secp256k1::Fq {
        <Secp256k1Affine as CurveAffine>::ScalarExt::random(rng)
    }

    // Returns (r, s)
    fn sign(
        rng: impl RngCore,
        sk: secp256k1::Fq,
        msg_hash: secp256k1::Fq,
    ) -> (secp256k1::Fq, secp256k1::Fq) {
        let randomness = <Secp256k1Affine as CurveAffine>::ScalarExt::random(rng);
        let randomness_inv = randomness.invert().unwrap();
        let generator = <Secp256k1Affine as PrimeCurveAffine>::generator();
        let sig_point = generator * randomness;
        let x = sig_point.to_affine().coordinates().unwrap().x().clone();

        let x_repr = &mut Vec::with_capacity(32);
        x.write(x_repr).unwrap();

        let mut x_bytes = [0u8; 64];
        x_bytes[..32].copy_from_slice(&x_repr[..]);

        let x_bytes_on_n = <Secp256k1Affine as CurveAffine>::ScalarExt::from_bytes_wide(&x_bytes); // get x cordinate (E::Base) on E::Scalar
        let sig_s = randomness_inv * (msg_hash + x_bytes_on_n * sk);
        (x_bytes_on_n, sig_s)
    }

    #[test]
    fn test_sign_verify() {
        let mut rng = XorShiftRng::seed_from_u64(1);
        const MAX_VERIF: usize = 2;
        const NUM_TXS: usize = 1;
        let mut txs = Vec::new();
        for _ in 0..NUM_TXS {
            let (sk, pk) = gen_key_pair(&mut rng);
            let msg_hash = gen_msg_hash(&mut rng);
            let sig = sign(&mut rng, sk, msg_hash);
            println!("DBG sk: {:#?}", sk);
            println!("DBG pk: {:#?}", pk);
            txs.push(TxSignData {
                signature: sig,
                pk,
                msg_hash,
            });
        }

        // generate a valid signature

        run::<Fr, MAX_VERIF>(txs);
    }
}

// Vectors using `XorShiftRng::seed_from_u64(1)`
// sk: 0x771bd7bf6c6414b9370bb8559d46e1cedb479b1836ea3c2e59a54c343b0d0495
// pk: (
//   0x8e31a3586d4c8de89d4e0131223ecfefa4eb76215f68a691ae607757d6256ede,
//   0xc76fdd462294a7eeb8ff3f0f698eb470f32085ba975801dbe446ed8e0b05400b
// )
// pk_hash: d90e2e9d267cbcfd94de06fa7adbe6857c2c733025c0b8938a76beeefc85d6c7
// addr: 0x7adbe6857c2c733025c0b8938a76beeefc85d6c7
