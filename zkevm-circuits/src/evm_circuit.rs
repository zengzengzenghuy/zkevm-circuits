//! The EVM circuit implementation.

#![allow(missing_docs)]
use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::*,
};

mod execution;
pub mod param;
pub(crate) mod step;
pub(crate) mod util;

pub mod table;

use crate::table::{BlockTable, BytecodeTable, CopyTable, ExpTable, KeccakTable, RwTable, TxTable};
use crate::util::{Challenges, SubCircuit, SubCircuitConfig};
pub use crate::witness;
use eth_types::Field;
use execution::ExecutionConfig;
use itertools::Itertools;
use strum::IntoEnumIterator;
use table::FixedTableTag;
use witness::Block;

/// EvmCircuitConfig implements verification of execution trace of a block.
#[derive(Clone, Debug)]
pub struct EvmCircuitConfig<F> {
    fixed_table: [Column<Fixed>; 4],
    byte_table: [Column<Fixed>; 1],
    pub(crate) execution: Box<ExecutionConfig<F>>,
    // External tables
    tx_table: TxTable,
    rw_table: RwTable,
    bytecode_table: BytecodeTable,
    block_table: BlockTable,
    copy_table: CopyTable,
    keccak_table: KeccakTable,
    exp_table: ExpTable,
}

/// Circuit configuration arguments
pub struct EvmCircuitConfigArgs<F: Field> {
    /// Power of randomness
    pub power_of_randomness: [Expression<F>; 31],
    /// TxTable
    pub tx_table: TxTable,
    /// RwTable
    pub rw_table: RwTable,
    /// BytecodeTable
    pub bytecode_table: BytecodeTable,
    /// BlockTable
    pub block_table: BlockTable,
    /// CopyTable
    pub copy_table: CopyTable,
    /// KeccakTable
    pub keccak_table: KeccakTable,
    /// ExpTable
    pub exp_table: ExpTable,
}

impl<F: Field> SubCircuitConfig<F> for EvmCircuitConfig<F> {
    type ConfigArgs = EvmCircuitConfigArgs<F>;

    /// Configure EvmCircuitConfig
    #[allow(clippy::too_many_arguments)]
    fn new(
        meta: &mut ConstraintSystem<F>,
        Self::ConfigArgs {
            power_of_randomness,
            tx_table,
            rw_table,
            bytecode_table,
            block_table,
            copy_table,
            keccak_table,
            exp_table,
        }: Self::ConfigArgs,
    ) -> Self {
        let fixed_table = [(); 4].map(|_| meta.fixed_column());
        let byte_table = [(); 1].map(|_| meta.fixed_column());
        let execution = Box::new(ExecutionConfig::configure(
            meta,
            power_of_randomness,
            &fixed_table,
            &byte_table,
            &tx_table,
            &rw_table,
            &bytecode_table,
            &block_table,
            &copy_table,
            &keccak_table,
            &exp_table,
        ));

        Self {
            fixed_table,
            byte_table,
            execution,
            tx_table,
            rw_table,
            bytecode_table,
            block_table,
            copy_table,
            keccak_table,
            exp_table,
        }
    }
}

impl<F: Field> EvmCircuitConfig<F> {
    /// Load fixed table
    pub fn load_fixed_table(
        &self,
        layouter: &mut impl Layouter<F>,
        fixed_table_tags: Vec<FixedTableTag>,
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "fixed table",
            |mut region| {
                for (offset, row) in std::iter::once([F::zero(); 4])
                    .chain(fixed_table_tags.iter().flat_map(|tag| tag.build()))
                    .enumerate()
                {
                    for (column, value) in self.fixed_table.iter().zip_eq(row) {
                        region.assign_fixed(|| "", *column, offset, || Value::known(value))?;
                    }
                }

                Ok(())
            },
        )
    }

    /// Load byte table
    pub fn load_byte_table(&self, layouter: &mut impl Layouter<F>) -> Result<(), Error> {
        layouter.assign_region(
            || "byte table",
            |mut region| {
                for offset in 0..256 {
                    region.assign_fixed(
                        || "",
                        self.byte_table[0],
                        offset,
                        || Value::known(F::from(offset as u64)),
                    )?;
                }

                Ok(())
            },
        )
    }

    /// Calculate which rows are "actually" used in the circuit
    pub fn get_active_rows(&self, block: &Block<F>) -> (Vec<usize>, Vec<usize>) {
        let max_offset = self.get_num_rows_required(block);
        // some gates are enabled on all rows
        let gates_row_ids = (0..max_offset).collect();
        // lookups are enabled at "q_step" rows and byte lookup rows
        let lookup_row_ids = (0..max_offset).collect();
        (gates_row_ids, lookup_row_ids)
    }

    pub fn get_num_rows_required(&self, block: &Block<F>) -> usize {
        // Start at 1 so we can be sure there is an unused `next` row available
        let mut num_rows = 1;
        let evm_rows = block.evm_circuit_pad_to;
        if evm_rows == 0 {
            for transaction in &block.txs {
                for step in &transaction.steps {
                    num_rows += self.execution.get_step_height(step.execution_state);
                }
            }
            num_rows += 1; // EndBlock
        } else {
            num_rows += block.evm_circuit_pad_to;
        }
        num_rows
    }
}

/// Tx Circuit for verifying transaction signatures
#[derive(Clone, Default, Debug)]
pub struct EvmCircuit<F: Field> {
    /// Block
    pub block: Option<Block<F>>,
    fixed_table_tags: Vec<FixedTableTag>,
}

impl<F: Field> EvmCircuit<F> {
    /// Return a new EvmCircuit
    pub fn new(block: Block<F>) -> Self {
        Self {
            block: Some(block),
            fixed_table_tags: FixedTableTag::iter().collect(),
        }
    }

    pub fn new_dev(block: Block<F>, fixed_table_tags: Vec<FixedTableTag>) -> Self {
        Self {
            block: Some(block),
            fixed_table_tags,
        }
    }
}

impl<F: Field> SubCircuit<F> for EvmCircuit<F> {
    type Config = EvmCircuitConfig<F>;

    fn new_from_block(block: &witness::Block<F>) -> Self {
        Self::new(block.clone())
    }

    /// Make the assignments to the EvmCircuit
    fn synthesize_sub(
        &self,
        config: &Self::Config,
        _challenges: &Challenges<Value<F>>,
        layouter: &mut impl Layouter<F>,
    ) -> Result<(), Error> {
        let block = self.block.as_ref().unwrap();

        config.load_fixed_table(layouter, self.fixed_table_tags.clone())?;
        config.load_byte_table(layouter)?;
        config.execution.assign_block(layouter, block)
    }
}

#[cfg(any(feature = "test", test))]
pub mod test {
    use super::*;
    use crate::{
        evm_circuit::{table::FixedTableTag, witness::Block, EvmCircuitConfig},
        table::{BlockTable, BytecodeTable, CopyTable, ExpTable, KeccakTable, RwTable, TxTable},
        util::{power_of_randomness_from_instance, Challenges},
        witness::block_convert,
    };
    use bus_mapping::{circuit_input_builder::CircuitsParams, evm::OpcodeId, mock::BlockData};
    use eth_types::{geth_types::GethData, Field, Word};
    use halo2_proofs::{
        circuit::{Layouter, SimpleFloorPlanner, Value},
        dev::{MockProver, VerifyFailure},
        plonk::{Circuit, ConstraintSystem, Error},
    };
    use rand::{
        distributions::uniform::{SampleRange, SampleUniform},
        random, thread_rng, Rng,
    };
    use strum::IntoEnumIterator;

    pub(crate) fn rand_range<T, R>(range: R) -> T
    where
        T: SampleUniform,
        R: SampleRange<T>,
    {
        thread_rng().gen_range(range)
    }

    pub(crate) fn rand_bytes(n: usize) -> Vec<u8> {
        (0..n).map(|_| random()).collect()
    }

    pub(crate) fn rand_bytes_array<const N: usize>() -> [u8; N] {
        [(); N].map(|_| random())
    }

    pub(crate) fn rand_word() -> Word {
        Word::from_big_endian(&rand_bytes_array::<32>())
    }

    /// create fixed_table_tags needed given witness block
    pub(crate) fn detect_fixed_table_tags<F: Field>(block: &Block<F>) -> Vec<FixedTableTag> {
        let need_bitwise_lookup = block.txs.iter().any(|tx| {
            tx.steps.iter().any(|step| {
                matches!(
                    step.opcode,
                    Some(OpcodeId::AND)
                        | Some(OpcodeId::OR)
                        | Some(OpcodeId::XOR)
                        | Some(OpcodeId::NOT)
                )
            })
        });
        FixedTableTag::iter()
            .filter(|t| {
                !matches!(
                    t,
                    FixedTableTag::BitwiseAnd
                        | FixedTableTag::BitwiseOr
                        | FixedTableTag::BitwiseXor
                ) || need_bitwise_lookup
            })
            .collect()
    }

    impl<F: Field> Circuit<F> for EvmCircuit<F> {
        type Config = EvmCircuitConfig<F>;
        type FloorPlanner = SimpleFloorPlanner;

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let tx_table = TxTable::construct(meta);
            let rw_table = RwTable::construct(meta);
            let bytecode_table = BytecodeTable::construct(meta);
            let block_table = BlockTable::construct(meta);
            let q_copy_table = meta.fixed_column();
            let copy_table = CopyTable::construct(meta, q_copy_table);
            let keccak_table = KeccakTable::construct(meta);
            let exp_table = ExpTable::construct(meta);

            let power_of_randomness = power_of_randomness_from_instance(meta);
            EvmCircuitConfig::new(
                meta,
                EvmCircuitConfigArgs {
                    power_of_randomness,
                    tx_table,
                    rw_table,
                    bytecode_table,
                    block_table,
                    copy_table,
                    keccak_table,
                    exp_table,
                },
            )
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            let block = self.block.as_ref().unwrap();
            let challenges = Challenges::mock(
                Value::known(block.randomness),
                Value::known(block.randomness),
            );

            config.tx_table.load(
                &mut layouter,
                &block.txs,
                block.circuits_params.max_txs,
                &challenges,
            )?;
            block.rws.check_rw_counter_sanity();
            config.rw_table.load(
                &mut layouter,
                &block.rws.table_assignments(),
                block.circuits_params.max_rws,
                Value::known(block.randomness),
            )?;
            config
                .bytecode_table
                .load(&mut layouter, block.bytecodes.values(), &challenges)?;
            config
                .block_table
                .load(&mut layouter, &block.context, block.randomness)?;
            config.copy_table.load(&mut layouter, block, &challenges)?;
            config
                .keccak_table
                .dev_load(&mut layouter, &block.sha3_inputs, &challenges)?;
            config.exp_table.load(&mut layouter, block)?;

            self.synthesize_sub(&config, &challenges, &mut layouter)
        }
    }

    impl<F: Field> EvmCircuit<F> {
        pub fn get_num_rows_required(block: &Block<F>) -> usize {
            let mut cs = ConstraintSystem::default();
            let config = EvmCircuit::<F>::configure(&mut cs);
            config.get_num_rows_required(block)
        }

        pub fn get_active_rows(block: &Block<F>) -> (Vec<usize>, Vec<usize>) {
            let mut cs = ConstraintSystem::default();
            let config = EvmCircuit::<F>::configure(&mut cs);
            config.get_active_rows(block)
        }
    }

    pub fn run_test_circuit_geth_data_default<F: Field>(
        block: GethData,
    ) -> Result<(), Vec<VerifyFailure>> {
        let mut builder =
            BlockData::new_from_geth_data_with_params(block.clone(), CircuitsParams::default())
                .new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();
        let block = block_convert(&builder.block, &builder.code_db).unwrap();
        run_test_circuit(block)
    }

    pub fn run_test_circuit_geth_data<F: Field>(
        block: GethData,
        circuits_params: CircuitsParams,
    ) -> Result<(), Vec<VerifyFailure>> {
        let mut builder = BlockData::new_from_geth_data_with_params(block.clone(), circuits_params)
            .new_circuit_input_builder();
        builder
            .handle_block(&block.eth_block, &block.geth_traces)
            .unwrap();
        let block = block_convert(&builder.block, &builder.code_db).unwrap();
        run_test_circuit(block)
    }

    pub fn get_test_degree<F: Field>(block: &Block<F>) -> u32 {
        let log2_ceil = |n| u32::BITS - (n as u32).leading_zeros() - (n & (n - 1) == 0) as u32;

        let num_rows_required_for_steps = EvmCircuit::<F>::get_num_rows_required(block);
        const NUM_BLINDING_ROWS: usize = 64;

        let fixed_table_tags = detect_fixed_table_tags(block);

        let k = log2_ceil(
            NUM_BLINDING_ROWS
                + fixed_table_tags
                    .iter()
                    .map(|tag| tag.build::<F>().count())
                    .sum::<usize>(),
        );
        let k = k.max(log2_ceil(
            NUM_BLINDING_ROWS
                + block
                    .bytecodes
                    .values()
                    .map(|bytecode| bytecode.bytes.len())
                    .sum::<usize>(),
        ));
        let k = k.max(log2_ceil(NUM_BLINDING_ROWS + num_rows_required_for_steps));
        let k = k.max(log2_ceil(NUM_BLINDING_ROWS + block.circuits_params.max_rws));
        log::debug!("evm circuit uses k = {}", k);

        k
    }

    pub fn get_test_cicuit_from_block<F: Field>(block: Block<F>) -> EvmCircuit<F> {
        let fixed_table_tags = detect_fixed_table_tags(&block);

        EvmCircuit::<F>::new_dev(block, fixed_table_tags)
    }

    pub fn get_test_instance<F: Field>(block: &Block<F>) -> Vec<Vec<F>> {
        let k = get_test_degree(block);

        (1..32)
            .map(|exp| vec![block.randomness.pow(&[exp, 0, 0, 0]); (1 << k) - 64])
            .collect()
    }

    pub fn run_test_circuit<F: Field>(block: Block<F>) -> Result<(), Vec<VerifyFailure>> {
        let k = get_test_degree(&block);

        let (active_gate_rows, active_lookup_rows) = EvmCircuit::<F>::get_active_rows(&block);

        let power_of_randomness = get_test_instance(&block);

        let circuit = get_test_cicuit_from_block(block);
        let prover = MockProver::<F>::run(k, &circuit, power_of_randomness).unwrap();
        prover.verify_at_rows_par(active_gate_rows.into_iter(), active_lookup_rows.into_iter())
    }
}

#[cfg(test)]
mod evm_circuit_stats {
    use super::test::*;
    use super::*;
    use crate::evm_circuit::step::ExecutionState;
    use eth_types::{bytecode, evm_types::OpcodeId, geth_types::GethData};
    use halo2_proofs::halo2curves::bn256::Fr;
    use halo2_proofs::plonk::ConstraintSystem;
    use mock::test_ctx::{helpers::*, TestContext};
    use strum::IntoEnumIterator;

    #[test]
    pub fn empty_evm_circuit() {
        let block: GethData = TestContext::<0, 0>::new(None, |_| {}, |_, _| {}, |b, _| b)
            .unwrap()
            .into();
        run_test_circuit_geth_data_default::<Fr>(block).unwrap();
    }

    /// This function prints to stdout a table with all the implemented states
    /// and their responsible opcodes with the following stats:
    /// - height: number of rows in the EVM circuit used by the execution state
    /// - gas: gas value used for the opcode execution
    /// - height/gas: ratio between circuit cost and gas cost
    ///
    /// Run with:
    /// `cargo test -p zkevm-circuits --release get_evm_states_stats --
    /// --nocapture --ignored`
    #[ignore]
    #[test]
    pub fn get_evm_states_stats() {
        let mut meta = ConstraintSystem::<Fr>::default();
        let circuit = EvmCircuit::configure(&mut meta);

        let mut implemented_states = Vec::new();
        for state in ExecutionState::iter() {
            let height = circuit.execution.get_step_height_option(state);
            if let Some(h) = height {
                implemented_states.push((state, h));
            }
        }

        let mut stats = Vec::new();
        for (state, h) in implemented_states {
            for opcode in state.responsible_opcodes() {
                let mut code = bytecode! {
                    PUSH2(0x8000)
                    PUSH2(0x00)
                    PUSH2(0x10)
                    PUSH2(0x20)
                    PUSH2(0x30)
                    PUSH2(0x40)
                    PUSH2(0x50)
                };
                code.write_op(opcode);
                code.write_op(OpcodeId::STOP);
                let block: GethData = TestContext::<2, 1>::new(
                    None,
                    account_0_code_account_1_no_code(code),
                    tx_from_1_to_0,
                    |block, _tx| block.number(0xcafeu64),
                )
                .unwrap()
                .into();
                let gas_cost = block.geth_traces[0].struct_logs[7].gas_cost.0;
                stats.push((state, opcode, h, gas_cost));
            }
        }

        println!(
            "| {: <14} | {: <14} | {: <2} | {: >6} | {: <5} |",
            "state", "opcode", "h", "g", "h/g"
        );
        println!("| ---            | ---            | ---|    --- | ---   |");
        for (state, opcode, height, gas_cost) in stats {
            println!(
                "| {: <14?} | {: <14?} | {: >2} | {: >6} | {: >1.3} |",
                state,
                opcode,
                height,
                gas_cost,
                height as f64 / gas_cost as f64
            );
        }
    }
}
