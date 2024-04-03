//! Conversion from a circuit that implements the `Air` trait into a halo2_backend compatible
//! circuit.  Includes helper functions to convert plonky3 witness format into halo2_backend
//! witness format.

extern crate alloc;

use halo2_middleware::circuit::{
    Any, Cell, ColumnMid, CompiledCircuitV2, ConstraintSystemMid, ExpressionMid, GateMid,
    PreprocessingV2, QueryMid, VarMid,
};
use halo2_middleware::ff::{Field, PrimeField};
use halo2_middleware::permutation;
use halo2_middleware::poly::Rotation;
use p3_air::Air;
use p3_matrix::dense::RowMajorMatrix;
use std::collections::HashMap;
use std::hash::Hash;

mod air;
mod fwrap;
mod symbolic_builder;
mod symbolic_expression;
mod symbolic_variable;

pub use air::*;
pub use fwrap::*;
pub use symbolic_builder::*;
pub use symbolic_expression::*;
pub use symbolic_variable::*;

fn fixed_query_r0<F: PrimeField + Hash>(index: usize) -> ExpressionMid<F> {
    ExpressionMid::Var(VarMid::Query(QueryMid {
        column_index: index,
        column_type: Any::Fixed,
        rotation: Rotation(0),
    }))
}

const LOCATION_COLUMNS: usize = 3; // First, Last, Transition
const COL_FIRST: usize = 0;
const COL_LAST: usize = 1;
const COL_TRANS: usize = 2;

// If the gate is enabled everywhere, transform it to only be enabled in usable rows
fn disable_in_unusable_rows<F: PrimeField + Hash>(
    e: &SymbolicExpression<FWrap<F>>,
) -> SymbolicExpression<FWrap<F>> {
    use SymbolicExpression as SE;
    match e {
        SE::Mul(lhs, _) => match &**lhs {
            SE::Location(_) => return e.clone(),
            _ => {}
        },
        _ => {}
    }
    let usable_location = SE::Location(Location::Transition) + SE::Location(Location::LastRow);
    usable_location * e.clone()
}

fn sym_to_expr<F: PrimeField + Hash>(e: &SymbolicExpression<FWrap<F>>) -> ExpressionMid<F> {
    use SymbolicExpression as SE;
    match e {
        SE::Variable(SymbolicVariable(Var::Query(query), _)) => {
            ExpressionMid::Var(VarMid::Query(QueryMid {
                column_index: query.column,
                column_type: Any::Advice,
                rotation: if query.is_next {
                    Rotation(1)
                } else {
                    Rotation(0)
                },
            }))
        }
        SE::Variable(SymbolicVariable(Var::Public(public), _)) => {
            panic!("unexpected public variable {:?} in expression", public)
        }
        SE::Location(Location::FirstRow) => fixed_query_r0(COL_FIRST),
        SE::Location(Location::LastRow) => fixed_query_r0(COL_LAST),
        SE::Location(Location::Transition) => fixed_query_r0(COL_TRANS),
        SE::Constant(c) => ExpressionMid::Constant(c.0),
        SE::Add(lhs, rhs) => sym_to_expr(lhs) + sym_to_expr(rhs),
        SE::Neg(e) => -sym_to_expr(e),
        SE::Mul(lhs, rhs) => sym_to_expr(lhs) * sym_to_expr(rhs),
    }
}

pub fn compile_preprocessing<F, A>(
    k: u32,
    size: usize,
    pre: &PreprocessingInfo,
    _air: &A,
) -> PreprocessingV2<F>
where
    F: PrimeField + Hash,
    A: Air<SymbolicAirBuilder<FWrap<F>>>,
{
    let n = 2usize.pow(k);
    let num_fixed_columns = LOCATION_COLUMNS;
    let mut fixed = vec![vec![F::ZERO; n]; num_fixed_columns];

    fixed[COL_FIRST][0] = F::ONE;
    fixed[COL_LAST][size - 1] = F::ONE;
    for i in 0..size - 1 {
        fixed[COL_TRANS][i] = F::ONE;
    }

    let mut copies = Vec::new();
    for (cell, public) in &pre.copy_public {
        let advice_row = match cell.1 {
            Location::FirstRow => 0,
            Location::LastRow => size - 1,
            Location::Transition => unreachable!(),
        };
        copies.push((
            Cell {
                column: ColumnMid {
                    column_type: Any::Advice,
                    index: cell.0,
                },
                row: advice_row,
            },
            Cell {
                column: ColumnMid {
                    column_type: Any::Instance,
                    index: 0,
                },
                row: *public,
            },
        ));
    }

    PreprocessingV2 {
        permutation: permutation::AssemblyMid { copies },
        fixed,
    }
}

// Check if the constraint is an equality against a public input and extract the copy constraint as
// `(advice_column_index, Location)` and `public_index`.  If there's no copy constriant, return
// None.
fn extract_copy_public<F: PrimeField + Hash>(
    e: &SymbolicExpression<FWrap<F>>,
) -> Option<((usize, Location), usize)> {
    use SymbolicExpression as SE;
    use SymbolicVariable as SV;
    // Example:
    // Mul(
    //   Location(FirstRow),
    //   Add(
    //     Variable(SymbolicVariable(Query(Query { is_next: false, column: 0 }))),
    //     Neg(Variable(SymbolicVariable(Public(Public { index: 0 }))))))
    let (mul_lhs, mul_rhs) = match e {
        SE::Mul(lhs, rhs) => (&**lhs, &**rhs),
        _ => return None,
    };
    let (cell_location, (add_lhs, add_rhs)) = match (mul_lhs, mul_rhs) {
        (SE::Location(location @ (Location::FirstRow | Location::LastRow)), SE::Add(lhs, rhs)) => {
            (*location, (&**lhs, &**rhs))
        }
        _ => return None,
    };
    let (cell_column, neg) = match (add_lhs, add_rhs) {
        (
            SE::Variable(SV(
                Var::Query(Query {
                    is_next: false,
                    column,
                }),
                _,
            )),
            SE::Neg(neg),
        ) => (*column, &**neg),
        _ => return None,
    };
    let public = match neg {
        SE::Variable(SV(Var::Public(Public { index }), _)) => *index,
        _ => return None,
    };
    Some(((cell_column, cell_location), public))
}

pub fn get_public_inputs<F: Field>(
    preprocessing_info: &PreprocessingInfo,
    size: usize,
    witness: &[Option<Vec<F>>],
) -> Vec<F> {
    let mut public_inputs = vec![F::ZERO; preprocessing_info.num_public_values];
    for (cell, public_index) in &preprocessing_info.copy_public {
        let offset = match cell.1 {
            Location::FirstRow => 0,
            Location::LastRow => size - 1,
            Location::Transition => unreachable!(),
        };
        public_inputs[*public_index] = witness[cell.0].as_ref().unwrap()[offset]
    }
    public_inputs
}

pub struct PreprocessingInfo {
    copy_public: Vec<((usize, Location), usize)>,
    num_public_values: usize,
}

pub fn compile_circuit_cs<F, A>(
    air: &A,
    num_public_values: usize,
    profiler: Option<dhat::Profiler>,
) -> (ConstraintSystemMid<F>, PreprocessingInfo)
where
    F: PrimeField + Hash,
    A: Air<SymbolicAirBuilder<FWrap<F>>>,
{
    let mut builder = SymbolicAirBuilder::new(air.width(), num_public_values);
    builder.profiler = profiler;
    println!("eval...");
    air.eval(&mut builder);

    println!("convert...");
    let num_fixed_columns = LOCATION_COLUMNS;
    let num_advice_columns = air.width();

    let mut gates: Vec<GateMid<F>> = Vec::new();
    // copy between `(advice_column_index, Location)` and `public_index`.
    let mut copy_public: Vec<((usize, Location), usize)> = Vec::new();
    let mut copy_columns: Vec<ColumnMid> = Vec::new();
    for (i, constraint) in builder.constraints.iter().enumerate() {
        // Check if the constraint is an equality against a public input and store it as a copy
        // constraint.  Otherwise it's a gate that can't have public variables.
        if let Some((cell, public)) = extract_copy_public(constraint) {
            copy_public.push((cell, public));
            let column = ColumnMid {
                column_type: Any::Advice,
                index: cell.0,
            };
            if !copy_columns.contains(&column) {
                copy_columns.push(column);
            }
            continue;
        };
        let constraint = disable_in_unusable_rows(constraint);
        gates.push(GateMid {
            name: format!("constraint{i}"),
            poly: sym_to_expr(&constraint),
        });
    }
    let mut num_instance_columns = 0;
    if !copy_public.is_empty() {
        copy_columns.push(ColumnMid {
            column_type: Any::Instance,
            index: 0,
        });
        num_instance_columns += 1;
    }

    let cs = ConstraintSystemMid::<F> {
        num_fixed_columns,
        num_advice_columns,
        num_instance_columns,
        num_challenges: 0,
        unblinded_advice_columns: Vec::new(),
        advice_column_phase: (0..num_advice_columns).map(|_| 0).collect(),
        challenge_phase: Vec::new(),
        gates,
        permutation: permutation::ArgumentMid {
            columns: copy_columns,
        },
        lookups: Vec::new(),
        shuffles: Vec::new(),
        general_column_annotations: HashMap::new(),
        minimum_degree: None,
    };
    (
        cs,
        PreprocessingInfo {
            copy_public,
            num_public_values,
        },
    )
}

pub fn trace_to_wit<F: Field>(k: u32, trace: RowMajorMatrix<FWrap<F>>) -> Vec<Option<Vec<F>>> {
    let n = 2usize.pow(k);
    let num_columns = trace.width;
    let mut witness = vec![vec![F::ZERO; n]; num_columns];
    for (row_offset, row) in trace.rows().enumerate() {
        for column_index in 0..num_columns {
            witness[column_index][row_offset] = row[column_index].0;
        }
    }
    witness.into_iter().map(Some).collect()
}

// TODO: Move to middleware
pub fn check_witness<F: Field>(
    circuit: &CompiledCircuitV2<F>,
    k: u32,
    witness: &[Option<Vec<F>>],
    public: &[&[F]],
) {
    let n = 2usize.pow(k);
    let cs = &circuit.cs;
    let preprocessing = &circuit.preprocessing;
    // Verify all gates
    for (i, gate) in cs.gates.iter().enumerate() {
        for offset in 0..n {
            let res = gate.poly.evaluate(
                &|s| s,
                &|v| match v {
                    VarMid::Query(q) => {
                        let offset = offset as i32 + q.rotation.0;
                        // TODO: Try to do mod n with a rust function
                        let offset = if offset < 0 {
                            (offset + n as i32) as usize
                        } else if offset >= n as i32 {
                            (offset - n as i32) as usize
                        } else {
                            offset as usize
                        };
                        match q.column_type {
                            Any::Instance => public[q.column_index][offset],
                            Any::Advice => witness[q.column_index].as_ref().unwrap()[offset],
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
                println!(
                    "Unsatisfied gate {} \"{}\" at offset {}",
                    i, gate.name, offset
                );
                panic!("KO");
            }
        }
    }
    println!("Check witness: OK");
}
