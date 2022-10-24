use super::{AccountMatch, StateTest, StateTestResult};
use crate::config::TestSuite;
use bus_mapping::circuit_input_builder::CircuitInputBuilder;
use bus_mapping::mock::BlockData;
use eth_types::{geth_types, Address, Bytes, GethExecTrace, U256, U64};
use ethers_core::k256::ecdsa::SigningKey;
use ethers_core::types::TransactionRequest;
use ethers_signers::{LocalWallet, Signer};
use external_tracer::TraceConfig;
use halo2_proofs::dev::CellValue;
use halo2_proofs::halo2curves::bn256::Fr;
use halo2_proofs::{
    dev::MockProver,
    plonk::{Any, Column},
};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use std::iter::Extend;
use std::{
    collections::{HashMap, HashSet},
    str::FromStr,
};
use thiserror::Error;
use zkevm_circuits::super_circuit::SuperCircuit;

const EVMERR_OOG: &str = "out of gas";
const EVMERR_STACKUNDERFLOW: &str = "stack underflow";
const EVMERR_GAS_UINT64OVERFLOW: &str = "gas uint64 overflow";

#[derive(PartialEq, Eq, Error, Debug)]
pub enum StateTestError {
    #[error("CannotGenerateCircuitInput({0})")]
    CircuitInput(String),
    #[error("VerifierError({0})")]
    VerifierError(String),
    #[error("BalanceMismatch(expected:{expected:?}, found:{found:?})")]
    BalanceMismatch { expected: U256, found: U256 },
    #[error("NonceMismatch(expected:{expected:?}, found:{found:?})")]
    NonceMismatch { expected: U256, found: U256 },
    #[error("CodeMismatch(expected: {expected:?}, found:{found:?})")]
    CodeMismatch { expected: Bytes, found: Bytes },
    #[error("StorgeMismatch(slot:{slot:?} expected:{expected:?}, found: {found:?})")]
    StorageMismatch {
        slot: U256,
        expected: U256,
        found: U256,
    },
    #[error("SkipTesstMaxGasLimit({0})")]
    SkipTestMaxGasLimit(u64),
    #[error("SkipTestMaxSteps({0})")]
    SkipTestMaxSteps(usize),
    #[error("SkipUnimplemented({0})")]
    SkipUnimplemented(String),
    #[error("Exception(expected:{expected:?}, found:{found:?})")]
    Exception { expected: bool, found: bool },
}

impl StateTestError {
    pub fn is_skip(&self) -> bool {
        matches!(
            self,
            StateTestError::SkipUnimplemented(_)
                | StateTestError::SkipTestMaxSteps(_)
                | StateTestError::SkipTestMaxGasLimit(_)
        )
    }
}

#[derive(Default, Debug, Clone)]
pub struct CircuitsConfig {
    pub super_circuit: bool,
}

fn check_post(
    builder: &CircuitInputBuilder,
    post: &HashMap<Address, AccountMatch>,
) -> Result<(), StateTestError> {
    // check if the generated account data is the expected one
    for (address, expected) in post {
        let (_, actual) = builder.sdb.get_account(address);

        if expected.balance.map(|v| v == actual.balance) == Some(false) {
            return Err(StateTestError::BalanceMismatch {
                expected: expected.balance.unwrap(),
                found: actual.balance,
            });
        }

        if expected.nonce.map(|v| v == actual.nonce) == Some(false) {
            return Err(StateTestError::NonceMismatch {
                expected: expected.nonce.unwrap(),
                found: actual.nonce,
            });
        }

        if let Some(expected_code) = &expected.code {
            let actual_code = if actual.code_hash.is_zero() {
                std::borrow::Cow::Owned(Vec::new())
            } else {
                std::borrow::Cow::Borrowed(&builder.code_db.0[&actual.code_hash])
            };
            if &actual_code as &[u8] != expected_code.0 {
                return Err(StateTestError::CodeMismatch {
                    expected: expected_code.clone(),
                    found: Bytes::from(actual_code.to_vec()),
                });
            }
        }
        for (slot, expected_value) in &expected.storage {
            let actual_value = actual.storage.get(slot).cloned().unwrap_or_else(U256::zero);
            if expected_value != &actual_value {
                return Err(StateTestError::StorageMismatch {
                    slot: *slot,
                    expected: *expected_value,
                    found: actual_value,
                });
            }
        }
    }
    Ok(())
}

fn into_traceconfig(st: StateTest) -> (String, TraceConfig, StateTestResult) {
    let chain_id = 1;
    let wallet = LocalWallet::from_str(&hex::encode(st.secret_key.0)).unwrap();
    let mut tx = TransactionRequest::new()
        .chain_id(chain_id)
        .from(st.from)
        .nonce(st.nonce)
        .value(st.value)
        .data(st.data.clone())
        .gas(st.gas_limit)
        .gas_price(st.gas_price);

    if let Some(to) = st.to {
        tx = tx.to(to);
    }

    let sig = wallet.sign_transaction_sync(&tx.into());

    (
        st.id,
        TraceConfig {
            chain_id: U256::one(),
            history_hashes: Vec::new(),
            block_constants: geth_types::BlockConstants {
                coinbase: st.env.current_coinbase,
                timestamp: U256::from(st.env.current_timestamp),
                number: U64::from(st.env.current_number),
                difficulty: st.env.current_difficulty,
                gas_limit: U256::from(st.env.current_gas_limit),
                base_fee: U256::one(),
            },

            transactions: vec![geth_types::Transaction {
                from: st.from,
                to: st.to,
                nonce: st.nonce,
                value: st.value,
                gas_limit: U256::from(st.gas_limit),
                gas_price: st.gas_price,
                gas_fee_cap: U256::zero(),
                gas_tip_cap: U256::zero(),
                call_data: st.data,
                access_list: None,
                v: sig.v,
                r: sig.r,
                s: sig.s,
            }],
            accounts: st.pre,
            ..Default::default()
        },
        st.result,
    )
}

pub fn geth_trace(st: StateTest) -> Result<GethExecTrace, StateTestError> {
    let (_, trace_config, _) = into_traceconfig(st);

    let mut geth_traces = external_tracer::trace(&trace_config)
        .map_err(|err| StateTestError::CircuitInput(err.to_string()))?;

    Ok(geth_traces.remove(0))
}

pub fn dump_mockprover(prover: &MockProver<Fr>) {
   
    let mut unique_columns: HashSet<&Column<Any>> = HashSet::new();
    prover
        .regions
        .iter()
        .for_each(|reg| unique_columns.extend(reg.columns.iter()));

    let column_names : HashMap<_,_> = unique_columns.into_iter().map(|col| {
        let offset = match col.column_type() {
          Any::Instance => unreachable!(),
          Any::Advice(_) => prover.instance.len(),
          Any::Fixed => prover.instance.len() + prover.advice.len(),
        };
        (offset + col.index(), col)
    }).collect();     

    let cols_count = prover.instance.len() + prover.advice.len() + prover.fixed.len();
    let header : Vec<_> = (0..cols_count).map(|n| {
        let mut text = if n >= prover.advice.len() + prover.instance.len() {
            format!("F {}", n - prover.instance.len() - prover.advice.len() )
        } else if n>= prover.instance.len()  {
            format!("A {}", n - prover.instance.len() )
        } else {
            format!("I {}", n )
        };
        if let Some(x) = column_names.get(&n) && !x.name().is_empty() {
            text.push(' ');
            text.push_str(x.name());
        }
        Cell::new(&text) 
    }).collect();        

    let advice_rows_count = prover.advice.get(0).unwrap_or(&vec![]).len();
    let fixed_rows_count = prover.fixed.get(0).unwrap_or(&vec![]).len();
    let instance_rows_count = prover.instance.get(0).unwrap_or(&vec![]).len();
    let rows_count = std::cmp::max(advice_rows_count, instance_rows_count);
    let rows_count = std::cmp::max(rows_count, fixed_rows_count);

    use prettytable::*;

    let mut table = Table::new();
    table.add_row(Row::new(header));

    let fr_cell = |n: &Fr| {
        let hex = format!("{:?}", n);
        let mut hexp = &hex[2..];
        while hexp.len()>1 && hexp.starts_with('0') {
            hexp = &hexp[1..];
        }

        if hexp.len() > 8 {
            Cell::new("BIG")
        } else {
            Cell::new(hexp)
        }
    };

    for row_idx in 0..rows_count {
        let mut row = Vec::new();
       
        for col_idx in 0..prover.instance.len(){
            row.push(match prover.instance[col_idx].get(row_idx) {
                Some(fr) => fr_cell(fr),
                None => Cell::new("")
            });
        }
        for col_idx in 0..prover.advice.len() {
            row.push(match prover.advice[col_idx].get(row_idx) {
                    Some(CellValue::Unassigned) => Cell::new(""),
                    Some(CellValue::Assigned(n)) => fr_cell(n),
                    Some(CellValue::Poison(_)) => Cell::new("X"),  
                    None => Cell::new("")
            });
        }
        for col_idx in 0..prover.fixed.len() {
            row.push(match prover.fixed[col_idx].get(row_idx) {
                    Some(CellValue::Unassigned) => Cell::new(""),
                    Some(CellValue::Assigned(n)) => fr_cell(n),
                    Some(CellValue::Poison(_)) => Cell::new("X"),  
                    None => Cell::new("")
            });
        }
        table.add_row(Row::new(row));
    }
    table.print_tty(false).unwrap();
}

pub fn run_test(
    st: StateTest,
    suite: TestSuite,
    circuits_config: CircuitsConfig,
) -> Result<(), StateTestError> {
    // get the geth traces

    let (_, trace_config, post) = into_traceconfig(st.clone());

    if st.to.is_none() {
        return Err(StateTestError::SkipUnimplemented(
            "TransactionCreation".to_string(),
        ));
    }

    let geth_traces = external_tracer::trace(&trace_config);
    if st.exception {
        if geth_traces.is_ok() {
            return Err(StateTestError::Exception {
                expected: st.exception,
                found: geth_traces.is_err(),
            });
        } else {
            return Ok(());
        }
    }

    let geth_traces = geth_traces.map_err(|err| StateTestError::CircuitInput(err.to_string()))?;

    if geth_traces[0].struct_logs.len() as u64 > suite.max_steps {
        return Err(StateTestError::SkipTestMaxSteps(
            geth_traces[0].struct_logs.len(),
        ));
    }

    // we are not checking here geth_traces[0].failed, since
    // there are some tests that makes the tx failing
    // (eg memory filler tests)

    if let Some(step) = geth_traces[0]
        .struct_logs
        .iter()
        .find(|step| suite.unimplemented_opcodes.contains(&step.op))
    {
        return Err(StateTestError::SkipUnimplemented(format!(
            "OPCODE {:?}",
            step.op
        )));
    }

    for err in [EVMERR_STACKUNDERFLOW, EVMERR_OOG, EVMERR_GAS_UINT64OVERFLOW] {
        if geth_traces[0]
            .struct_logs
            .iter()
            .any(|step| step.error.as_ref().map(|e| e.contains(err)) == Some(true))
        {
            return Err(StateTestError::SkipUnimplemented(format!("Error {}", err)));
        }
    }

    if geth_traces[0].gas.0 > suite.max_gas {
        return Err(StateTestError::SkipTestMaxGasLimit(geth_traces[0].gas.0));
    }

    if let Some(acc) = st.pre.get(&st.to.unwrap()) {
        if acc.code.0.is_empty() {
            return Err(StateTestError::SkipUnimplemented(
                "Calling to empty accounts unimplemented (1)".to_string(),
            ));
        }
    } else {
        return Err(StateTestError::SkipUnimplemented(
            "Calling to empty accounts unimplemented (2)".to_string(),
        ));
    }

    let transactions = trace_config
        .transactions
        .into_iter()
        .enumerate()
        .map(|(index, tx)| eth_types::Transaction {
            from: tx.from,
            to: tx.to,
            value: tx.value,
            input: tx.call_data,
            gas_price: Some(tx.gas_price),
            access_list: tx.access_list,
            nonce: tx.nonce,
            gas: tx.gas_limit,
            transaction_index: Some(U64::from(index)),
            ..eth_types::Transaction::default()
        })
        .collect();

    let eth_block = eth_types::Block {
        author: Some(trace_config.block_constants.coinbase),
        timestamp: trace_config.block_constants.timestamp,
        number: Some(U64::from(trace_config.block_constants.number.as_u64())),
        difficulty: trace_config.block_constants.difficulty,
        gas_limit: trace_config.block_constants.gas_limit,
        base_fee_per_gas: Some(trace_config.block_constants.base_fee),
        transactions,
        ..eth_types::Block::default()
    };

    let wallet: LocalWallet = SigningKey::from_bytes(&st.secret_key).unwrap().into();
    let mut wallets = HashMap::new();
    wallets.insert(wallet.address(), wallet.with_chain_id(1u64));

    // process the transaction
    let mut geth_data = eth_types::geth_types::GethData {
        chain_id: trace_config.chain_id,
        history_hashes: trace_config.history_hashes.clone(),
        geth_traces: geth_traces.clone(),
        accounts: trace_config.accounts.values().cloned().collect(),
        eth_block: eth_block.clone(),
    };

    let mut builder;

    if !circuits_config.super_circuit {
        let block_data = BlockData::new_from_geth_data(geth_data);

        builder = block_data.new_circuit_input_builder();
        builder
            .handle_block(&eth_block, &geth_traces)
            .map_err(|err| StateTestError::CircuitInput(err.to_string()))?;

        let block =
            zkevm_circuits::evm_circuit::witness::block_convert(&builder.block, &builder.code_db);

        let (evm_prover, evm_gate_rows, evm_lookup_rows) =
            zkevm_circuits::evm_circuit::test::build_mockprover(block.clone());
        let (state_prover, state_gate_rows, state_lookup_rows) =
            zkevm_circuits::state_circuit::dev::build_mockprover(block);

        dump_mockprover(&evm_prover);

        evm_prover
            .verify_at_rows(evm_gate_rows.into_iter(), evm_lookup_rows.into_iter())
            .map_err(|err| StateTestError::VerifierError(format!("{:#?}", err)))?;

        state_prover
            .verify_at_rows(state_gate_rows.into_iter(), state_lookup_rows.into_iter())
            .map_err(|err| StateTestError::VerifierError(format!("{:#?}", err)))?;
    } else {
        geth_data.sign(&wallets);

        let (k, circuit, instance, _builder) =
            SuperCircuit::<_, 1, 32>::build(geth_data, &mut ChaCha20Rng::seed_from_u64(2)).unwrap();
        builder = _builder;

        let prover = MockProver::run(k, &circuit, instance).unwrap();
        dump_mockprover(&prover);
        prover
            .verify_par()
            .map_err(|err| StateTestError::VerifierError(format!("{:#?}", err)))?;
    }

    check_post(&builder, &post)?;

    Ok(())
}
