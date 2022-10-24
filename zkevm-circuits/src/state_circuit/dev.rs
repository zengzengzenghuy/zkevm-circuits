/// TODO
use eth_types::Field;
use halo2_proofs::dev::MockProver;

use crate::{witness::Block, state_circuit::StateCircuit};
/// TODO
pub fn build_mockprover<F: Field>(block: Block<F>) -> (MockProver<F>, Vec<usize>, Vec<usize>) {
    const N_ROWS: usize = 1 << 16;
    let state_circuit = StateCircuit::new(block.randomness, block.rws, N_ROWS);
    let power_of_randomness = state_circuit.instance();
    let gate_row_ids =   ( N_ROWS - state_circuit.rows.len()..N_ROWS).collect();
    let lookup_input_row_ids = (N_ROWS - state_circuit.rows.len()..N_ROWS).collect();
    (
        MockProver::run(18, &state_circuit, power_of_randomness).unwrap(),
        gate_row_ids,
        lookup_input_row_ids
    )
}