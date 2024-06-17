use halo2_middleware::circuit::{
    Any, Cell, ColumnMid, CompiledCircuit, ConstraintSystemMid, ExpressionMid, GateMid,
    Preprocessing, QueryMid, VarMid,
};
use halo2_middleware::ff::{Field, PrimeField};
use rand_chacha::ChaCha20Rng;
use rand_core::{RngCore, SeedableRng};

fn rotate(n: usize, offset: usize, rotation: i32) -> usize {
    let offset = offset as i32 + rotation;
    if offset < 0 {
        (offset + n as i32) as usize
    } else if offset >= n as i32 {
        (offset - n as i32) as usize
    } else {
        offset as usize
    }
}

/// Check that the wintess passes all the constraints defined by the circuit.  Panics if any
/// constraint is not satisfied.
pub fn check_witness<F: Field>(
    circuit: &CompiledCircuit<F>,
    k: u32,
    blinding_rows: usize,
    witness: &[Vec<F>],
    public: &[Vec<F>],
) {
    let n = 2usize.pow(k);
    let usable_rows = n - blinding_rows;
    let cs = &circuit.cs;
    let preprocessing = &circuit.preprocessing;

    // Calculate blinding values
    let mut rng = ChaCha20Rng::seed_from_u64(0xdeadbeef);
    let mut blinders = vec![vec![F::ZERO; blinding_rows]; cs.num_advice_columns];
    for column_blinders in blinders.iter_mut() {
        for v in column_blinders.iter_mut() {
            *v = F::random(&mut rng);
        }
    }

    let mut blinded = vec![true; cs.num_advice_columns];
    for advice_column_index in &cs.unblinded_advice_columns {
        blinded[*advice_column_index] = false;
    }

    // Verify all gates
    for (i, gate) in cs.gates.iter().enumerate() {
        for offset in 0..n {
            let res = gate.poly.evaluate(
                &|s| s,
                &|v| match v {
                    VarMid::Query(q) => {
                        let offset = rotate(n, offset, q.rotation.0);
                        match q.column_type {
                            Any::Instance => public[q.column_index][offset],
                            Any::Advice => {
                                if offset >= usable_rows && blinded[q.column_index] {
                                    blinders[q.column_index][offset - usable_rows]
                                } else {
                                    witness[q.column_index][offset]
                                }
                            }
                            Any::Fixed => preprocessing.fixed[q.column_index][offset],
                        }
                    }
                    VarMid::Challenge(_c) => unimplemented!(),
                },
                &|ne| -ne,
                &|a, b| a + b,
                &|a, b| a * b,
            );
            if !res.is_zero_vartime() {
                panic!(
                    "Unsatisfied gate {} \"{}\" at offset {}",
                    i, gate.name, offset
                );
            }
        }
    }
}
