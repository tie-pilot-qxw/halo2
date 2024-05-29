use crate::circuit::{
    Any, Cell, ChallengeMid, ColumnMid, ConstraintSystemMid, ExpressionMid, GateMid, Preprocessing,
    QueryMid, VarMid,
};
use crate::expression::Expression;
use crate::ff::Field;
use crate::lookup;
use crate::permutation;
use crate::shuffle;
use std::cmp::max;
use std::collections::HashMap;

pub struct LinkConfig {
    /// List of shared advice columns.  Each entry corresponds to a shared advice column between
    /// multiple circuit as Vec of pairs of circuit index and column index.
    pub shared_advice_columns: Vec<Vec<(usize, usize)>>,
    /// List of shared fixed columns.  Each entry corresponds to a shared fixed column between
    /// multiple circuit as Vec of pairs of circuit index and column index.
    pub shared_fixed_columns: Vec<Vec<(usize, usize)>>,
    /// List of shared challenges.  Each entry corresponds to a shared challenge between
    /// multiple circuit as Vec of pairs of circuit index and challenge index.
    pub shared_challenges: Vec<Vec<(usize, usize)>>,
    /// Merge strategy for each shared advice column
    pub witness_merge_strategy: Vec<MergeStrategy>,
    /// Merge strategy for each shared fixed column
    pub fixed_merge_strategy: Vec<MergeStrategy>,
}

pub struct Map {
    // Mappings from (circuit_index, local_column_index) to global_column_index
    advice_column: HashMap<(usize, usize), usize>,
    fixed_column: HashMap<(usize, usize), usize>,
    instance_column: HashMap<(usize, usize), usize>,
    // Mapping from (circuit_index, local_challenge_index) to global challenge
    challenge: HashMap<(usize, usize), ChallengeMid>,
}

fn column_to_global_index(
    circuit_index: usize,
    map: &Map,
    column_type: Any,
    local_index: usize,
) -> usize {
    match column_type {
        Any::Advice => *map
            .advice_column
            .get(&(circuit_index, local_index))
            .unwrap(),
        Any::Fixed => *map.fixed_column.get(&(circuit_index, local_index)).unwrap(),
        Any::Instance => *map
            .instance_column
            .get(&(circuit_index, local_index))
            .unwrap(),
    }
}

fn column_to_global(circuit_index: usize, map: &Map, column: &ColumnMid) -> ColumnMid {
    ColumnMid {
        column_type: column.column_type,
        index: column_to_global_index(circuit_index, &map, column.column_type, column.index),
    }
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
        Var(Query(q)) => Var(Query(QueryMid {
            column_index: column_to_global_index(circuit_index, map, q.column_type, q.column_index),
            column_type: q.column_type,
            rotation: q.rotation,
        })),
        Var(Challenge(c)) => Var(Challenge(
            *map.challenge.get(&(circuit_index, c.index)).unwrap(),
        )),
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
    cfg: &LinkConfig,
    css: &[ConstraintSystemMid<F>],
) -> (ConstraintSystemMid<F>, Map) {
    let mut num_fixed_columns = 0;
    let mut num_advice_columns = 0;
    let mut num_instance_columns = 0;
    let mut num_challenges = 0;
    let mut unblinded_advice_columns = Vec::new();
    let mut advice_column_phase = Vec::new();
    let mut challenge_phase = Vec::new();
    let mut minimum_degree = None;
    let mut map = Map {
        advice_column: HashMap::new(),
        fixed_column: HashMap::new(),
        instance_column: HashMap::new(),
        challenge: HashMap::new(),
    };

    // Allocate shared challenges
    for (global_challenge_index, shared_challenge) in cfg.shared_challenges.iter().enumerate() {
        let mut phase = None;
        for (circuit_index, local_challenge_index) in shared_challenge {
            // check that shared challenges are in the same phase
            if let Some(phase) = phase {
                assert_eq!(
                    phase,
                    css[*circuit_index].challenge_phase[*local_challenge_index]
                );
            } else {
                phase = Some(css[*circuit_index].challenge_phase[*local_challenge_index]);
            }
            map.challenge.insert(
                (*circuit_index, *local_challenge_index),
                ChallengeMid {
                    index: global_challenge_index,
                    phase: phase.unwrap(),
                },
            );
        }
        challenge_phase.push(phase.unwrap());
    }
    num_challenges += cfg.shared_challenges.len();

    // In the global circuit we first allocate the shared columns and then the independent ones.
    for (global_column_index, shared_advice_column) in cfg.shared_advice_columns.iter().enumerate()
    {
        let mut unblinded = None;
        let mut phase = None;
        for (circuit_index, local_column_index) in shared_advice_column {
            // check that shared advice columns have the same unblinding setting
            if let Some(unblinded) = unblinded {
                assert_eq!(
                    unblinded,
                    css[*circuit_index]
                        .unblinded_advice_columns
                        .contains(local_column_index)
                );
            } else {
                unblinded = Some(
                    css[*circuit_index]
                        .unblinded_advice_columns
                        .contains(local_column_index),
                );
            }
            // check that shared advice columns are in the same phase
            if let Some(phase) = phase {
                assert_eq!(
                    phase,
                    css[*circuit_index].advice_column_phase[*local_column_index]
                );
            } else {
                phase = Some(css[*circuit_index].advice_column_phase[*local_column_index]);
            }
            map.advice_column
                .insert((*circuit_index, *local_column_index), global_column_index);
        }
        advice_column_phase.push(phase.unwrap());
        if unblinded.unwrap() {
            unblinded_advice_columns.push(global_column_index);
        }
    }
    num_advice_columns += cfg.shared_advice_columns.len();

    for (global_column_index, shared_fixed_column) in cfg.shared_fixed_columns.iter().enumerate() {
        for (circuit_index, local_column_index) in shared_fixed_column {
            map.fixed_column
                .insert((*circuit_index, *local_column_index), global_column_index);
        }
    }
    num_fixed_columns += cfg.shared_fixed_columns.len();

    for (circuit_index, cs) in css.iter().enumerate() {
        // Advices
        for local_column_index in 0..cs.num_advice_columns {
            if !map
                .advice_column
                .contains_key(&(circuit_index, local_column_index))
            {
                map.advice_column
                    .insert((circuit_index, local_column_index), num_advice_columns);
                advice_column_phase.push(cs.advice_column_phase[local_column_index]);
                if cs.unblinded_advice_columns.contains(&local_column_index) {
                    unblinded_advice_columns.push(num_advice_columns);
                }
                num_advice_columns += 1;
            }
        }

        // Fixed
        for local_column_index in 0..cs.num_fixed_columns {
            if !map
                .fixed_column
                .contains_key(&(circuit_index, local_column_index))
            {
                map.fixed_column
                    .insert((circuit_index, local_column_index), num_fixed_columns);
                num_fixed_columns += 1;
            }
        }

        // Instance
        for local_column_index in 0..cs.num_instance_columns {
            if !map
                .instance_column
                .contains_key(&(circuit_index, local_column_index))
            {
                map.instance_column
                    .insert((circuit_index, local_column_index), num_instance_columns);
                num_instance_columns += 1;
            }
        }

        // Challenges
        for local_challenge_index in 0..cs.num_challenges {
            if !map
                .challenge
                .contains_key(&(circuit_index, local_challenge_index))
            {
                let phase = cs.challenge_phase[local_challenge_index];
                map.challenge.insert(
                    (circuit_index, local_challenge_index),
                    ChallengeMid {
                        index: num_challenges,
                        phase,
                    },
                );
                num_challenges += 1;
                challenge_phase.push(phase);
            }
        }

        minimum_degree = match (minimum_degree, cs.minimum_degree) {
            (Some(global), Some(local)) => Some(max(global, local)),
            (Some(global), None) => Some(global),
            (None, Some(local)) => Some(local),
            (None, None) => None,
        };
    }

    let mut general_column_annotations = HashMap::new();
    for (circuit_index, cs) in css.iter().enumerate() {
        for (column, name) in &cs.general_column_annotations {
            general_column_annotations
                .insert(column_to_global(circuit_index, &map, column), name.clone());
        }
    }

    // Translate all the expressions to use the global columns
    let mut gates = Vec::new();
    let mut lookups = Vec::new();
    let mut shuffles = Vec::new();
    let mut permutation = permutation::ArgumentMid {
        columns: Vec::new(),
    };
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
        for column in &cs.permutation.columns {
            permutation
                .columns
                .push(column_to_global(circuit_index, &map, column));
        }
    }

    (
        ConstraintSystemMid {
            num_fixed_columns,
            num_advice_columns,
            num_instance_columns,
            num_challenges,
            unblinded_advice_columns,
            advice_column_phase,
            challenge_phase,
            gates,
            permutation,
            lookups,
            shuffles,
            general_column_annotations,
            minimum_degree,
        },
        map,
    )
}

pub fn link_preprocessing<F: Field>(
    cfg: &LinkConfig,
    cs: &ConstraintSystemMid<F>,
    map: &Map,
    preprocessings: Vec<Preprocessing<F>>,
) -> Preprocessing<F> {
    let merge_strategy = &cfg.fixed_merge_strategy;
    assert_eq!(merge_strategy.len(), cfg.shared_fixed_columns.len());
    for (global_column_index, strategy) in merge_strategy.iter().enumerate() {
        if let MergeStrategy::Main(circuit_index, column_index) = strategy {
            assert!(cfg.shared_fixed_columns[global_column_index]
                .contains(&(*circuit_index, *column_index)));
        }
    }

    let mut fixed = vec![Vec::new(); cs.num_fixed_columns];
    let mut permutation = permutation::AssemblyMid { copies: Vec::new() };
    for (circuit_index, preprocessing) in preprocessings.into_iter().enumerate() {
        for (local_index, fixed_column) in preprocessing.fixed.into_iter().enumerate() {
            let global_index = map.fixed_column.get(&(circuit_index, local_index)).unwrap();
            let merge_strategy = merge_strategy.get(*global_index);
            if let Some(merge_strategy) = merge_strategy {
                column_merge(
                    merge_strategy,
                    circuit_index,
                    local_index,
                    &mut fixed[*global_index],
                    fixed_column,
                );
            } else {
                fixed[*global_index] = fixed_column;
            }
        }
        for (cell_lhs, cell_rhs) in &preprocessing.permutation.copies {
            let cell_lhs = Cell {
                column: column_to_global(circuit_index, &map, &cell_lhs.column),
                row: cell_lhs.row,
            };
            let cell_rhs = Cell {
                column: column_to_global(circuit_index, &map, &cell_rhs.column),
                row: cell_rhs.row,
            };
            permutation.copies.push((cell_lhs, cell_rhs));
        }
    }
    Preprocessing { permutation, fixed }
}

pub enum MergeStrategy {
    // Expect all the duplicated witness columns to have equal assignments.
    ExpectEqual,
    // When a pair of duplicated witness column differ in the assignment at a particular row, if
    // one of them is 0 and the other is not, we take the non-zero value.  We don't allow two
    // non-zero different values in the same row.
    OverwriteZeros,
    // From all the duplicated witness columns, use the assignment from (circuit_index,
    // column_index).
    Main(usize, usize),
}

#[derive(Default)]
pub struct LinkWitnessConfig {
    // Merge strategy for each shared advice column
    pub merge_strategy: Vec<MergeStrategy>,
}

fn column_merge<F: Field>(
    strategy: &MergeStrategy,
    src_circuit_index: usize,
    src_column_index: usize,
    column_dst: &mut Vec<F>,
    column_src: Vec<F>,
) {
    use MergeStrategy::*;
    match strategy {
        ExpectEqual => {
            if !column_dst.is_empty() {
                assert_eq!(*column_dst, column_src);
            } else {
                *column_dst = column_src;
            }
        }
        OverwriteZeros => {
            if !column_dst.is_empty() {
                column_dst
                    .iter_mut()
                    .zip(column_src)
                    .for_each(|(cell_dst, cell_src)| {
                        if cell_dst.is_zero_vartime() {
                            *cell_dst = cell_src;
                        } else {
                            assert_eq!(*cell_dst, cell_src)
                        }
                    });
            } else {
                *column_dst = column_src;
            }
        }
        Main(circuit_index, column_index) => {
            // println!(
            //     "merge main ({}, {}) - ({}, {})",
            //     circuit_index, column_index, src_circuit_index, src_column_index
            // );
            if *circuit_index == src_circuit_index && *column_index == src_column_index {
                *column_dst = column_src;
            }
        }
    }
}

pub fn link_witness<F: Field>(
    cfg: &LinkConfig,
    cs: &ConstraintSystemMid<F>,
    map: &Map,
    witnesses: Vec<Vec<Option<Vec<F>>>>,
) -> Vec<Option<Vec<F>>> {
    let merge_strategy = &cfg.witness_merge_strategy;
    assert_eq!(merge_strategy.len(), cfg.shared_advice_columns.len());
    for (global_column_index, strategy) in merge_strategy.iter().enumerate() {
        if let MergeStrategy::Main(circuit_index, column_index) = strategy {
            assert!(cfg.shared_advice_columns[global_column_index]
                .contains(&(*circuit_index, *column_index)));
        }
    }

    let mut witness: Vec<Option<Vec<F>>> = vec![None; cs.num_advice_columns];
    for (circuit_index, witness_columns) in witnesses.into_iter().enumerate() {
        for (local_index, witness_column) in witness_columns.into_iter().enumerate() {
            let global_index = map
                .advice_column
                .get(&(circuit_index, local_index))
                .unwrap();
            let merge_strategy = merge_strategy.get(*global_index);
            if let Some(merge_strategy) = merge_strategy {
                if witness_column.is_some() {
                    // Allocate an empty column for the first time
                    if witness[*global_index].is_none() {
                        witness[*global_index] = Some(Vec::new());
                    }
                    column_merge(
                        merge_strategy,
                        circuit_index,
                        local_index,
                        &mut witness[*global_index].as_mut().unwrap(),
                        witness_column.unwrap(),
                    );
                }
            } else {
                witness[*global_index] = witness_column;
            }
        }
    }
    witness
}
