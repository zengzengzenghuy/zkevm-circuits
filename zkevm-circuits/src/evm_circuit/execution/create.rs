use crate::{
    evm_circuit::{
        execution::ExecutionGadget,
        param::{N_BYTES_ACCOUNT_ADDRESS, N_BYTES_GAS, N_BYTES_MEMORY_WORD_SIZE},
        step::ExecutionState,
        util::{
            common_gadget::TransferGadget,
            constraint_builder::{
                ConstraintBuilder, ReversionInfo, StepStateTransition,
                Transition::{Delta, To},
            },
            from_bytes,
            math_gadget::{
                BatchedIsZeroGadget, ConstantDivisionGadget, IsEqualGadget, IsZeroGadget,
                MinMaxGadget,
            },
            memory_gadget::{MemoryAddressGadget, MemoryExpansionGadget},
            select, sum, CachedRegion, Cell, Word,
        },
        witness::{Block, Call, ExecStep, Transaction},
    },
    table::{AccountFieldTag, CallContextFieldTag},
    util::Expr,
};
use bus_mapping::evm::OpcodeId;
use eth_types::{
    evm_types::{GasCost, GAS_STIPEND_CALL_WITH_VALUE},
    Field, ToLittleEndian, ToScalar, U256,
};
use halo2_proofs::{circuit::Value, plonk::Error};
use keccak256::EMPTY_HASH_LE;

/// Gadget for CREATE and CREATE2 opcodes
#[derive(Clone, Debug)]
pub(crate) struct CreateGadget<F> {
    opcode: Cell<F>,
    is_create2: Cell<F>,
    // // tx access list for new address
    // tx_id: Cell<F>,
    // is_warm_prev: Cell<F>,
    // caller_reversion_info: ReversionInfo<F>,
    //
    // // transfer value to new address
    // transfer: TransferGadget<F>,
    // callee_reversion_info: ReversionInfo<F>,
    //
    // // memory
    // caller_memory_address: MemoryAddressGadget<F>,
    // memory_expansion: MemoryExpansionGadget<F, 1, N_BYTES_MEMORY_WORD_SIZE>,
    // // new call context
    // current_address: Cell<F>,
    // depth: Cell<F>,
    // gas: Word<F>,
    // callee_address: Word<F>,
    // value: Word<F>,
    // is_success: Cell<F>,
    // gas_is_u64: IsZeroGadget<F>,
    //
    // // gas
    // one_64th_gas: ConstantDivisionGadget<F, N_BYTES_GAS>,
    // capped_callee_gas_left: MinMaxGadget<F, N_BYTES_GAS>,

    // errors:
    // is_empty_nonce_and_balance: BatchedIsZeroGadget<F, 2>,
    // is_empty_code_hash: IsEqualGadget<F>,
}

impl<F: Field> ExecutionGadget<F> for CreateGadget<F> {
    const NAME: &'static str = "CREATE";

    const EXECUTION_STATE: ExecutionState = ExecutionState::CREATE;

    fn configure(cb: &mut ConstraintBuilder<F>) -> Self {
        let opcode = cb.query_cell();
        cb.opcode_lookup(opcode.expr(), 1.expr());

        let is_create2 = cb.query_bool();
        cb.require_equal(
            "Opcode is CREATE or CREATE2",
            opcode.expr(),
            select::expr(
                is_create2.expr(),
                OpcodeId::CREATE2.expr(),
                OpcodeId::CREATE.expr(),
            ),
        );

        // let mut reversion_info = cb.reversion_info_read(None);
        // let is_warm_prev = cb.query_bool();
        // let tx_id = cb.call_context(None, CallContextFieldTag::TxId);
        // cb.account_access_list_write(
        //     tx_id.expr(),
        //     callee_address.clone(),
        //     1.expr(),
        //     is_warm_prev.expr(),
        //     Some(&mut reversion_info),
        // );
        // // let access_list = AccountAccessListGadget::construct(cb,
        // // callee_address.expr()); cb.add_account_to_access_list(callee_address.
        // // expr());
        //
        // let caller_address = cb.call_context(None,
        // CallContextFieldTag::CalleeAddress); let [callee_address, value,
        // callee_address] = [(); 3].map(|| cb.query_word()); let is_failure =
        // IsZeroGadget::construct(cb, callee_address);
        // let mut callee_reversion_info =
        //     ReversionInfo::from_caller(cb, &reversion_info,
        // not::expr(is_failure.expr())); let transfer =
        // TransferGadget::construct(     cb,
        //     caller_address.expr(),
        //     address.expr(),
        //     value.expr(),
        //     &mut callee_reversion_info,
        // );

        // let [offset, size] = [(); 2].map(|| cb.query_word());
        // let memory_address = MemoryAddressGadget::construct(cb, offset, size);
        // let memory_expansion = MemoryExpansionGadget::construct(
        //     cb,
        //     cb.curr.state.memory_word_size.expr(),
        //     [memory_address.address()],
        // );
        //
        // let [value, offset, size, salt, address] = [(); 5].map(cb.query_cell());
        // [value, offset, size].map(|cell| cb.stack_pop(cell.expr()));
        // cb.condition(is_create2.expr(), |cb| cb.stack_pop(salt.expr()));
        // cb.stack_push(address);
        //
        // let [current_address, is_static, depth] = [
        //     CallContextFieldTag::CalleeAddress,
        //     CallContextFieldTag::IsStatic,
        //     CallContextFieldTag::Depth,
        // ]
        // .map(|field_tag| cb.call_context(None, field_tag));
        //
        // cb.range_lookup(depth.expr(), 1024);
        //
        // // Lookup values from stack
        // cb.stack_pop(gas_word.expr());
        // cb.stack_pop(callee_address_word.expr());

        // // `CALL` opcode has an additional stack pop `value`.
        // cb.condition(IS_CREATE2.expr(), |cb| cb.stack_pop(value.expr()));
        //
        // [
        //     cd_offset.expr(),
        //     cd_length.expr(),
        //     rd_offset.expr(),
        //     rd_length.expr(),
        // ]
        // .map(|expression| cb.stack_pop(expression));
        // cb.stack_push(is_success.expr());

        // let gas = Eip150Gadget::construct(cb, cb.curr.state.gas_left.expr() -
        // GasCost::CREATE);
        //
        // cb.require_step_state_transition(StepStateTransition {
        //     rw_counter: Delta(cb.rw_counter_offset.clone()),
        //     call_id: To(callee_call_id.expr()),
        //     is_root: To(false.expr()),
        //     is_create: To(true.expr()),
        //     code_hash: To(initialization_code_hash.expr()),
        //     gas_left: To(gas.callee_gas_left()),
        //     reversible_write_counter: To(2.expr()),
        //     ..StepStateTransition::new_context()
        // });

        Self { opcode, is_create2 }
    }

    fn assign_exec_step(
        &self,
        region: &mut CachedRegion<'_, '_, F>,
        offset: usize,
        block: &Block<F>,
        _: &Transaction,
        call: &Call,
        step: &ExecStep,
    ) -> Result<(), Error> {
        let opcode = step.opcode.unwrap();
        self.opcode.assign(
            region,
            offset,
            Value::known(F::from(opcode.as_u64())),
        )?;
        self.is_create2.assign(
            region,
            offset,
            Value::known((opcode == OpcodeId::CREATE2).to_scalar().unwrap()),
        )?;
        Ok(())
    }
}
