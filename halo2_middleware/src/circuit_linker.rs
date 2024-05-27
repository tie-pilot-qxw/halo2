use crate::circuit::{Any, ConstraintSystemMid, ExpressionMid, GateMid, QueryMid, VarMid};
use crate::expression::Expression;
use crate::ff::Field;
use crate::lookup;
use crate::shuffle;
use std::collections::HashMap;

pub struct LinkConfig {
    /// List of shared advice columns.  Each entry corresponds to a shared advice column between
    /// multiple circuit as Vec of pairs of circuit index and column index.
    pub shared_advice_columns: Vec<Vec<(usize, usize)>>,
}

struct Map {
    // Mapping from (circuit_index, local_column_index) to global_column_index
    advice_column: HashMap<(usize, usize), usize>,
}

fn expr_to_global<F: Field>(
    circuit_index: usize,
    map: &Map,
    expr: &ExpressionMid<F>,
) -> ExpressionMid<F> {
    use Expression::*;
    use VarMid::*;
    match expr {
        Constant(f) => Constant(f.clone()),
        Var(Query(q)) => {
            let column_index = match q.column_type {
                Any::Advice => *map
                    .advice_column
                    .get(&(circuit_index, q.column_index))
                    .unwrap(),
                Any::Fixed => q.column_index,
                Any::Instance => q.column_index,
            };
            Var(Query(QueryMid {
                column_index,
                column_type: q.column_type,
                rotation: q.rotation,
            }))
        }
        Var(Challenge(c)) => Var(Challenge(c.clone())),
        Negated(e) => Negated(Box::new(expr_to_global(circuit_index, map, e))),
        Sum(e1, e2) => Sum(
            Box::new(expr_to_global(circuit_index, map, e1)),
            Box::new(expr_to_global(circuit_index, map, e2)),
        ),
        Product(e1, e2) => Product(
            Box::new(expr_to_global(circuit_index, map, e1)),
            Box::new(expr_to_global(circuit_index, map, e2)),
        ),
    }
}

pub fn link_cs<F: Field>(
    css: &[ConstraintSystemMid<F>],
    cfg: &LinkConfig,
) -> ConstraintSystemMid<F> {
    let mut num_advice_columns = 0;
    let mut map = Map {
        advice_column: HashMap::new(),
    };

    // Sanity checks
    // TODO: Check that shared columns have the same
    // - unblinded setting
    // - phase

    // TODO: Add shared challenge in config
    // - Check that shared challenges are in the same phase

    // In the global circuit we first allocate the shared columns and then the independent ones.
    for (global_column_index, shared_advice_column) in cfg.shared_advice_columns.iter().enumerate()
    {
        for (circuit_index, local_column_index) in shared_advice_column {
            map.advice_column
                .insert((*circuit_index, *local_column_index), global_column_index);
        }
    }
    num_advice_columns += cfg.shared_advice_columns.len();
    for (circuit_index, cs) in css.iter().enumerate() {
        for local_column_index in 0..cs.num_advice_columns {
            if !map
                .advice_column
                .contains_key(&(circuit_index, local_column_index))
            {
                map.advice_column
                    .insert((circuit_index, local_column_index), num_advice_columns);
                num_advice_columns += 1;
            }
        }
    }

    // Translate all the expressions to use the global columns
    let mut gates = Vec::new();
    let mut lookups = Vec::new();
    let mut shuffles = Vec::new();
    for (circuit_index, cs) in css.iter().enumerate() {
        for gate in &cs.gates {
            let poly = expr_to_global(circuit_index, &map, &gate.poly);
            gates.push(GateMid {
                name: gate.name.clone(),
                poly,
            });
        }
        for lookup in &cs.lookups {
            let input_expressions = lookup
                .input_expressions
                .iter()
                .map(|expr| expr_to_global(circuit_index, &map, expr))
                .collect();
            let table_expressions = lookup
                .table_expressions
                .iter()
                .map(|expr| expr_to_global(circuit_index, &map, expr))
                .collect();
            lookups.push(lookup::ArgumentMid {
                name: lookup.name.clone(),
                input_expressions,
                table_expressions,
            });
        }
        for shuffle in &cs.shuffles {
            let input_expressions = shuffle
                .input_expressions
                .iter()
                .map(|expr| expr_to_global(circuit_index, &map, expr))
                .collect();
            let shuffle_expressions = shuffle
                .shuffle_expressions
                .iter()
                .map(|expr| expr_to_global(circuit_index, &map, expr))
                .collect();
            shuffles.push(shuffle::ArgumentMid {
                name: shuffle.name.clone(),
                input_expressions,
                shuffle_expressions,
            });
        }
    }
    todo!()
    // ConstraintSystemMid {
    //     num_fixed_columns,
    //     num_advice_columns,
    //     num_instance_columns,
    //     num_challenges,
    // }
}
