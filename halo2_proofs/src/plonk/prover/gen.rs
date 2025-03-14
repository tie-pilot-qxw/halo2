//! Generator for [`create_proof`]
use crate::plonk::{evaluation::EvaluationData, ColumnType, Expression};
use crate::poly::commitment::ParamsProver;

use super::*;
use ff::PrimeField;
use std::collections::BTreeMap;
use std::{any, marker::PhantomData};
use zkpoly_compiler::{
    ast::{self, PolyLagrange},
    transit::{type2, HashTyp},
};
use zkpoly_runtime::{self as rt, args::RuntimeType};

enum PolyOrScalar<Rt: RuntimeType> {
    Poly(ast::PolyLagrange<Rt>),
    Scalar(ast::Scalar<Rt>),
}

impl<Rt: RuntimeType> PolyOrScalar<Rt> {
    pub fn unwrap_poly(&self) -> ast::PolyLagrange<Rt> {
        match self {
            PolyOrScalar::Poly(poly) => poly.clone(),
            _ => panic!("called unwrap_poly on a scalar"),
        }
    }
}

fn evaluate_expression<Rt: RuntimeType, const USE_EXT: bool>(
    expr: &Expression<Rt::Field>,
    table: &Table<Rt>,
    challenges: &[ast::Scalar<Rt>],
    rot_scale: i32,
) -> PolyOrScalar<Rt> {
    match expr {
        Expression::Constant(c) => PolyOrScalar::Scalar(ast::Scalar::constant(c.clone())),
        Expression::Selector(..) => panic!("virtual selectors are removed during optimization"),
        Expression::Fixed(query) => {
            let poly = if USE_EXT {
                table.fixed_exts[query.column_index].clone()
            } else {
                table.fixed_values[query.column_index].clone()
            };
            PolyOrScalar::Poly(poly.rotate(query.rotation.0 * rot_scale))
        }
        Expression::Advice(query) => {
            let poly = if USE_EXT {
                table.advice_exts[query.column_index].clone()
            } else {
                table.advice_values[query.column_index].clone()
            };
            PolyOrScalar::Poly(poly.rotate(query.rotation.0 * rot_scale))
        }
        Expression::Instance(query) => {
            let poly = if USE_EXT {
                table.instance_exts[query.column_index].clone()
            } else {
                table.instance_values[query.column_index].clone()
            };
            PolyOrScalar::Poly(poly.rotate(query.rotation.0 * rot_scale))
        }
        Expression::Challenge(value) => PolyOrScalar::Scalar(challenges[value.index()].clone()),
        Expression::Negated(expr) => {
            let negated = evaluate_expression::<_, USE_EXT>(expr, table, challenges, rot_scale);
            match &negated {
                PolyOrScalar::Scalar(scalar) => PolyOrScalar::Scalar(-scalar.clone()),
                PolyOrScalar::Poly(p) => PolyOrScalar::Poly(-p.clone()),
            }
        }
        Expression::Sum(lhs, rhs) => {
            let lhs = evaluate_expression::<_, USE_EXT>(lhs, table, challenges, rot_scale);
            let rhs = evaluate_expression::<_, USE_EXT>(rhs, table, challenges, rot_scale);
            match (&lhs, &rhs) {
                (PolyOrScalar::Scalar(lhs), PolyOrScalar::Scalar(rhs)) => {
                    PolyOrScalar::Scalar(lhs.clone() + rhs.clone())
                }
                (PolyOrScalar::Poly(lhs), PolyOrScalar::Scalar(rhs)) => {
                    PolyOrScalar::Poly(lhs.clone() + rhs.clone())
                }
                (PolyOrScalar::Scalar(lhs), PolyOrScalar::Poly(rhs)) => {
                    PolyOrScalar::Poly(lhs.clone() + rhs.clone())
                }
                (PolyOrScalar::Poly(lhs), PolyOrScalar::Poly(rhs)) => {
                    PolyOrScalar::Poly(lhs.clone() + rhs.clone())
                }
            }
        }
        Expression::Product(lhs, rhs) => {
            let lhs = evaluate_expression::<_, USE_EXT>(lhs, table, challenges, rot_scale);
            let rhs = evaluate_expression::<_, USE_EXT>(rhs, table, challenges, rot_scale);
            match (&lhs, &rhs) {
                (PolyOrScalar::Scalar(lhs), PolyOrScalar::Scalar(rhs)) => {
                    PolyOrScalar::Scalar(lhs.clone() * rhs.clone())
                }
                (PolyOrScalar::Poly(lhs), PolyOrScalar::Scalar(rhs)) => {
                    PolyOrScalar::Poly(lhs.clone() * rhs.clone())
                }
                (PolyOrScalar::Scalar(lhs), PolyOrScalar::Poly(rhs)) => {
                    PolyOrScalar::Poly(lhs.clone() * rhs.clone())
                }
                (PolyOrScalar::Poly(lhs), PolyOrScalar::Poly(rhs)) => {
                    PolyOrScalar::Poly(lhs.clone() * rhs.clone())
                }
            }
        }
        Expression::Scaled(lhs, rhs) => {
            let lhs = evaluate_expression::<_, USE_EXT>(lhs, table, challenges, rot_scale);
            let rhs = ast::Scalar::constant(rhs.clone());
            match &lhs {
                PolyOrScalar::Scalar(lhs) => PolyOrScalar::Scalar(lhs.clone() * rhs.clone()),
                PolyOrScalar::Poly(lhs) => PolyOrScalar::Poly(lhs.clone() * rhs.clone()),
            }
        }
    }
}

fn compress_expressions<Rt: RuntimeType>(
    vertices: impl Iterator<Item = ast::PolyLagrange<Rt>>,
    theta: &ast::Scalar<Rt>,
    n: u64,
) -> ast::PolyLagrange<Rt> {
    vertices.fold(ast::PolyLagrange::zeros(n), |acc, v| {
        acc * theta.clone() + v
    })
}

mod user_functions {
    use super::*;
    use zkpoly_compiler::{ast::user_function as uf, transit::type2};
    use zkpoly_runtime::error::RuntimeError;

    pub type CalculateAdvicesF<Rt: RuntimeType, CC> = uf::FunctionOnce3<
        Rt,
        ast::Array<Rt, ast::PolyLagrange<Rt>>,
        ast::Whatever<Rt, HashMap<usize, Rt::Field>>,
        ast::Whatever<Rt, CC>,
        ast::Array<Rt, ast::PolyLagrange<Rt>>,
    >;

    pub fn calculate_advices<
        'params,
        Rt: RuntimeType,
        ConcreteCircuit: Circuit<Rt::Field> + 'static + Send + Sync,
    >(
        n: u64,
        k: u32,
        current_phase: sealed::Phase,
        meta: &ConstraintSystem<Rt::Field>,
        config: ConcreteCircuit::Config,
    ) -> CalculateAdvicesF<Rt, ConcreteCircuit>
    where
        ConcreteCircuit::Config: 'static + Send + Sync,
    {
        #[derive(Clone)]
        struct AdviceSingle<C: CurveAffine, B: Basis> {
            pub advice_polys: Vec<Polynomial<C::Scalar, B>>,
            pub advice_blinds: Vec<Blind<C::Scalar>>,
        }

        struct WitnessCollection<'a, F: Field> {
            k: u32,
            current_phase: sealed::Phase,
            advice: Vec<Polynomial<Assigned<F>, LagrangeCoeff>>,
            unblinded_advice: HashSet<usize>,
            challenges: &'a HashMap<usize, F>,
            instances: Vec<&'a rt::scalar::ScalarArray<F>>,
            usable_rows: RangeTo<usize>,
            _marker: std::marker::PhantomData<F>,
        }

        impl<'a, F: Field> Assignment<F> for WitnessCollection<'a, F> {
            fn enter_region<NR, N>(&mut self, _: N)
            where
                NR: Into<String>,
                N: FnOnce() -> NR,
            {
                // Do nothing; we don't care about regions in this context.
            }

            fn exit_region(&mut self) {
                // Do nothing; we don't care about regions in this context.
            }

            fn enable_selector<A, AR>(&mut self, _: A, _: &Selector, _: usize) -> Result<(), Error>
            where
                A: FnOnce() -> AR,
                AR: Into<String>,
            {
                // We only care about advice columns here

                Ok(())
            }

            fn annotate_column<A, AR>(&mut self, _annotation: A, _column: Column<Any>)
            where
                A: FnOnce() -> AR,
                AR: Into<String>,
            {
                // Do nothing
            }

            fn query_instance(
                &self,
                column: Column<Instance>,
                row: usize,
            ) -> Result<Value<F>, Error> {
                if !self.usable_rows.contains(&row) {
                    return Err(Error::not_enough_rows_available(self.k));
                }

                self.instances
                    .get(column.index())
                    .and_then(|column| Some(column[row]))
                    .map(|v| Value::known(v))
                    .ok_or(Error::BoundsFailure)
            }

            fn assign_advice<V, VR, A, AR>(
                &mut self,
                _: A,
                column: Column<Advice>,
                row: usize,
                to: V,
            ) -> Result<(), Error>
            where
                V: FnOnce() -> Value<VR>,
                VR: Into<Assigned<F>>,
                A: FnOnce() -> AR,
                AR: Into<String>,
            {
                // Ignore assignment of advice column in different phase than current one.
                if self.current_phase != column.column_type().phase {
                    return Ok(());
                }

                if !self.usable_rows.contains(&row) {
                    return Err(Error::not_enough_rows_available(self.k));
                }

                *self
                    .advice
                    .get_mut(column.index())
                    .and_then(|v| v.get_mut(row))
                    .ok_or(Error::BoundsFailure)? = to().into_field().assign()?;

                Ok(())
            }

            fn assign_fixed<V, VR, A, AR>(
                &mut self,
                _: A,
                _: Column<Fixed>,
                _: usize,
                _: V,
            ) -> Result<(), Error>
            where
                V: FnOnce() -> Value<VR>,
                VR: Into<Assigned<F>>,
                A: FnOnce() -> AR,
                AR: Into<String>,
            {
                // We only care about advice columns here

                Ok(())
            }

            fn copy(
                &mut self,
                _: Column<Any>,
                _: usize,
                _: Column<Any>,
                _: usize,
            ) -> Result<(), Error> {
                // We only care about advice columns here

                Ok(())
            }

            fn fill_from_row(
                &mut self,
                _: Column<Fixed>,
                _: usize,
                _: Value<Assigned<F>>,
            ) -> Result<(), Error> {
                Ok(())
            }

            fn get_challenge(&self, challenge: Challenge) -> Value<F> {
                self.challenges
                    .get(&challenge.index())
                    .cloned()
                    .map(Value::known)
                    .unwrap_or_else(Value::unknown)
            }

            fn push_namespace<NR, N>(&mut self, _: N)
            where
                NR: Into<String>,
                N: FnOnce() -> NR,
            {
                // Do nothing; we don't care about namespaces in this context.
            }

            fn pop_namespace(&mut self, _: Option<String>) {
                // Do nothing; we don't care about namespaces in this context.
            }
        }

        let unusable_rows_start = n as usize - (meta.blinding_factors() + 1);
        let num_advice_columns = meta.num_advice_columns;
        let unblinded_advice_columns = meta.unblinded_advice_columns.clone();
        let constants = meta.constants.clone();

        let f = move |mut r: Vec<&mut zkpoly_runtime::scalar::ScalarArray<Rt::Field>>,
                      instances: Vec<&zkpoly_runtime::scalar::ScalarArray<Rt::Field>>,
                      challenges: &HashMap<usize, Rt::Field>,
                      circuit: &ConcreteCircuit| {
            let mut witness = WitnessCollection {
                k,
                current_phase,
                advice: vec![Polynomial::empty_lagrange_assigned(n as usize); num_advice_columns],
                unblinded_advice: HashSet::from_iter(unblinded_advice_columns.iter().copied()),
                instances,
                challenges,
                // The prover will not be allowed to assign values to advice
                // cells that exist within inactive rows, which include some
                // number of blinding factors and an extra row for use in the
                // permutation argument.
                usable_rows: ..unusable_rows_start,
                _marker: std::marker::PhantomData,
            };

            // Synthesize the circuit to obtain the witness and other information.
            ConcreteCircuit::FloorPlanner::synthesize(&mut witness, circuit, config, constants)
                .map_err(|e| RuntimeError::Other(format!("{:?}", e)))?;

            let r_dominators = r.split_off(num_advice_columns);
            let r_numerators = r;

            witness
                .advice
                .into_iter()
                .zip(r_numerators.into_iter())
                .zip(r_dominators.into_iter())
                .for_each(|((advice, r_numerators), r_dominators)| {
                    advice
                        .values
                        .into_iter()
                        .zip(r_numerators.iter_mut())
                        .zip(r_dominators.iter_mut())
                        .for_each(|((assigned, r_numerator), r_dominator)| {
                            let (n, d) = match assigned {
                                Assigned::Zero => (Rt::Field::ZERO, Rt::Field::ONE),
                                Assigned::Trivial(x) => (x, Rt::Field::ONE),
                                Assigned::Rational(n0, d0) => (n0, d0),
                            };
                            *r_numerator = n;
                            *r_dominator = d;
                        });
                });
            Ok(())
        };

        uf::FunctionOnce3::new(
            "calculate_advices".to_string(),
            f,
            type2::Typ::Array(Box::new(type2::Typ::lagrange(n)), 2 * num_advice_columns),
        )
    }

    pub type NewHashDictF<Rt: RuntimeType, K, T> =
        uf::FunctionFn0<Rt, ast::Whatever<Rt, HashMap<K, T>>>;

    pub fn new_hash_dict<Rt: RuntimeType, K: 'static + Send + Sync, T: 'static + Send + Sync>(
    ) -> NewHashDictF<Rt, K, T> {
        let f = |r: Box<dyn FnOnce(HashMap<K, T>) + '_>| {
            r(HashMap::new());
            Ok(())
        };

        uf::FunctionFn0::new(
            format!(
                "new_hash_dict::<{}, {}>",
                any::type_name::<K>(),
                any::type_name::<T>()
            ),
            f,
            type2::Typ::Any(
                any::TypeId::of::<HashMap<K, T>>(),
                std::mem::size_of::<HashMap<K, T>>(),
            ),
        )
    }

    pub fn hash_dict_insert<Rt: RuntimeType>(
        k: usize,
    ) -> uf::FunctionFn2<
        Rt,
        ast::Whatever<Rt, HashMap<usize, Rt::Field>>,
        ast::Scalar<Rt>,
        ast::Whatever<Rt, HashMap<usize, Rt::Field>>,
    > {
        let f = move |r: Box<dyn FnOnce(HashMap<usize, Rt::Field>) + '_>,
                      hd: &HashMap<usize, Rt::Field>,
                      t: &rt::scalar::Scalar<Rt::Field>| {
            let mut hd = hd.clone();
            hd.insert(k, t.to_ff());
            r(hd);
            Ok(())
        };

        uf::FunctionFn2::new(
            "hash_dict_insert".to_string(),
            f,
            type2::Typ::Any(
                any::TypeId::of::<HashMap<usize, rt::scalar::Scalar<Rt::Field>>>(),
                std::mem::size_of::<HashMap<usize, rt::scalar::Scalar<Rt::Field>>>(),
            ),
        )
    }

    pub fn collect_challenges<Rt: RuntimeType>(
        num_challenges: usize,
    ) -> uf::FunctionFn1<
        Rt,
        ast::Whatever<Rt, HashMap<usize, Rt::Field>>,
        ast::Array<Rt, ast::Scalar<Rt>>,
    > {
        let f = move |r: Vec<&mut rt::scalar::Scalar<Rt::Field>>,
                      challenges: &HashMap<usize, Rt::Field>| {
            let result = (0..num_challenges)
                .map(|index| challenges[&index].clone())
                .collect::<Vec<_>>();
            result.into_iter().zip(r.into_iter()).for_each(|(x, y)| {
                *y.as_mut() = x;
            });
            Ok(())
        };

        uf::FunctionFn1::new(
            "collect_challenges".to_string(),
            f,
            type2::Typ::Array(Box::new(type2::Typ::Scalar), num_challenges),
        )
    }

    pub type PermuteExpressionPairF<Rt: RuntimeType> = uf::FunctionFn2<
        Rt,
        ast::PolyLagrange<Rt>,
        ast::PolyLagrange<Rt>,
        ast::Tuple2<ast::PolyLagrange<Rt>, ast::PolyLagrange<Rt>, Rt>,
    >;

    pub fn permute_expression_pair<'params, Rt: RuntimeType>(
        blinding_factors: usize,
        n: u64,
    ) -> PermuteExpressionPairF<Rt>
    where
        Rt::Field: Ord,
    {
        let usable_rows = n as usize - (blinding_factors + 1);
        let f = move |r: (
            &mut rt::scalar::ScalarArray<Rt::Field>,
            &mut rt::scalar::ScalarArray<Rt::Field>,
        ),
                      a: &rt::scalar::ScalarArray<Rt::Field>,
                      b: &rt::scalar::ScalarArray<Rt::Field>| {
            let mut permuted_input_expression: Vec<_> = a.iter().copied().collect();
            permuted_input_expression.truncate(usable_rows);

            // Sort input lookup expression values
            permuted_input_expression.sort();

            // A BTreeMap of each unique element in the table expression and its count
            let mut leftover_table_map: BTreeMap<Rt::Field, u32> =
                b.iter()
                    .take(usable_rows)
                    .fold(BTreeMap::new(), |mut acc, coeff| {
                        *acc.entry(*coeff).or_insert(0) += 1;
                        acc
                    });
            let mut permuted_table_coeffs = vec![Rt::Field::ZERO; usable_rows];

            let mut repeated_input_rows = permuted_input_expression
                .iter()
                .zip(permuted_table_coeffs.iter_mut())
                .enumerate()
                .filter_map(|(row, (input_value, table_value))| {
                    // If this is the first occurrence of `input_value` in the input expression
                    if row == 0 || *input_value != permuted_input_expression[row - 1] {
                        *table_value = *input_value;
                        // Remove one instance of input_value from leftover_table_map
                        if let Some(count) = leftover_table_map.get_mut(input_value) {
                            assert!(*count > 0);
                            *count -= 1;
                            None
                        } else {
                            // Return error if input_value not found
                            Some(Err(Error::ConstraintSystemFailure))
                        }
                    // If input value is repeated
                    } else {
                        Some(Ok(row))
                    }
                })
                .collect::<Result<Vec<_>, _>>()
                .map_err(|err| rt::error::RuntimeError::Other(format!("{:?}", err)))?;

            // Populate permuted table at unfilled rows with leftover table elements
            for (coeff, count) in leftover_table_map.iter() {
                for _ in 0..*count {
                    permuted_table_coeffs[repeated_input_rows.pop().unwrap()] = *coeff;
                }
            }
            assert!(repeated_input_rows.is_empty());

            assert_eq!(permuted_input_expression.len(), usable_rows);
            assert_eq!(permuted_table_coeffs.len(), usable_rows);

            r.0.iter_mut()
                .zip(r.1.iter_mut())
                .zip(
                    permuted_input_expression
                        .into_iter()
                        .zip(permuted_table_coeffs.into_iter()),
                )
                .for_each(|((ri, rt), (i, t))| {
                    *ri = i;
                    *rt = t;
                });

            Ok(())
        };

        uf::FunctionFn2::new(
            "permute_expression_pair".to_string(),
            f,
            type2::Typ::Tuple(vec![
                type2::Typ::lagrange(usable_rows as u64),
                type2::Typ::lagrange(usable_rows as u64),
            ]),
        )
    }

    pub type EvaluateVanishingPolynomailF<Rt: RuntimeType> =
        uf::FunctionFn2<Rt, ast::Array<Rt, ast::Scalar<Rt>>, ast::Scalar<Rt>, ast::Scalar<Rt>>;

    pub fn evaluate_vanishing_polynomial<Rt: RuntimeType>() -> EvaluateVanishingPolynomailF<Rt> {
        let f = |r: &mut rt::scalar::Scalar<Rt::Field>,
                 roots: Vec<&rt::scalar::Scalar<Rt::Field>>,
                 z: &rt::scalar::Scalar<Rt::Field>| {
            let roots: Vec<_> = roots.into_iter().map(|x| x.to_ff()).collect();
            let eval = crate::arithmetic::evaluate_vanishing_polynomial(&roots, z.to_ff());
            *r = rt::scalar::Scalar::from_ff(&eval);
            Ok(())
        };

        uf::FunctionFn2::new(
            "evaluate_vanishing_polynomial".to_string(),
            f,
            type2::Typ::Scalar,
        )
    }
}

struct PermutedPlookupArgument<Rt: RuntimeType> {
    ci_values: ast::PolyLagrange<Rt>,
    ct_values: ast::PolyLagrange<Rt>,
    pi_values: ast::PolyLagrange<Rt>,
    pt_values: ast::PolyLagrange<Rt>,
    pi_coef: ast::PolyCoef<Rt>,
    pt_coef: ast::PolyCoef<Rt>,
}

fn compute_permuted_for_plookup<Rt: RuntimeType>(
    pa: &lookup::Argument<Rt::Field>,
    theta: &ast::Scalar<Rt>,
    table: &Table<Rt>,
    challenges: &[ast::Scalar<Rt>],
    n: u64,
    unusable_rows_start: u64,
    permutater: &user_functions::PermuteExpressionPairF<Rt>,
) -> PermutedPlookupArgument<Rt> {
    let inputs_evaluated = pa
        .input_expressions
        .iter()
        .map(|expr| evaluate_expression::<_, false>(expr, table, challenges, 1).unwrap_poly())
        .collect::<Vec<_>>();
    let tables_evaluated = pa
        .table_expressions
        .iter()
        .map(|expr| evaluate_expression::<_, false>(expr, table, challenges, 1).unwrap_poly())
        .collect::<Vec<_>>();
    let ci_values = compress_expressions(inputs_evaluated.iter().cloned(), theta, n);
    let ct_values = compress_expressions(tables_evaluated.iter().cloned(), theta, n);

    let ci_values = ci_values.extend(n).blind(unusable_rows_start, n);
    let ct_values = ct_values.extend(n).blind(unusable_rows_start, n);

    let (pi_values, pt_values) = permutater
        .call(ci_values.clone(), ct_values.clone())
        .unpack();

    let pt_coef = pt_values.to_coef();
    let pi_coef = pi_values.to_coef();

    PermutedPlookupArgument {
        ci_values,
        ct_values,
        pi_values,
        pt_values,
        pi_coef,
        pt_coef,
    }
}

fn compute_permutation_ppp<Rt: RuntimeType>(
    columns: &Vec<Column<Any>>,
    ppk: &ProvingKey<Rt::PointAffine>,
    permutations: &[ast::PolyLagrange<Rt>],
    n: u64,
    table: &Table<Rt>,
    beta: &ast::Scalar<Rt>,
    gamma: &ast::Scalar<Rt>,
    omega_powers: &ast::PolyLagrange<Rt>,
    delta: &ast::Scalar<Rt>,
) -> Vec<ast::PolyLagrange<Rt>> {
    let chunk_len = ppk.vk.cs_degree - 2;
    let blinding_factors = ppk.vk.cs.blinding_factors();
    let unusable_rows_start = n as usize - (blinding_factors + 1);

    let mut modified_values = ast::PolyLagrange::ones(n);
    let mut last_z = ast::Scalar::one();

    let mut delta_power = ast::Scalar::one();

    let sets = columns
        .chunks(chunk_len)
        .zip(permutations.chunks(chunk_len))
        .map(|(columns, permutations)| {
            for (column, permuted_column_values) in columns.iter().zip(permutations.iter()) {
                let column_values = table.lagrange(*column);
                modified_values = modified_values.clone()
                    * (beta.clone() * permuted_column_values.clone()
                        + gamma.clone()
                        + column_values.clone());
                modified_values = modified_values.clone()
                    * (omega_powers.clone() * beta.clone() * delta_power.clone()
                        + gamma.clone()
                        + column_values);

                delta_power = delta_power.clone() * delta.clone();
            }

            let z = modified_values.scan_mul(&last_z);
            let z = z.blind(unusable_rows_start as u64, n);
            last_z = z.index(n - (blinding_factors as u64 + 1));

            z
        })
        .collect();

    sets
}

fn compute_lookup_ppp<Rt: RuntimeType>(
    ppa: &PermutedPlookupArgument<Rt>,
    beta: &ast::Scalar<Rt>,
    gamma: &ast::Scalar<Rt>,
    unusable_rows_start: u64,
    n: u64,
) -> ast::PolyLagrange<Rt> {
    let z = (beta.clone() + ppa.ci_values.clone()) * (gamma.clone() + ppa.ct_values.clone());
    let z = z / (beta.clone() + ppa.pi_values.clone()) * (gamma.clone() + ppa.pt_values.clone());
    let z = z.scan_mul(&ast::Scalar::one());
    let z = z.blind(unusable_rows_start, n);
    z
}

fn construct_primary_constraint<Rt: RuntimeType>(
    h: &mut ast::PolyLagrange<Rt>,
    pk_permutation_exts: &[ast::PolyLagrange<Rt>],
    permutation_ppps: &[ast::PolyLagrange<Rt>],
    las: &[lookup::Argument<Rt::Field>],
    plas: &[PermutedPlookupArgument<Rt>],
    lookup_ppp_coefs: &[ast::PolyCoef<Rt>],
    table: &Table<Rt>,
    pk: &ProvingKey<Rt::PointAffine>,
    challenges: &[ast::Scalar<Rt>],
    zetas: &ast::PolyLagrange<Rt>,
    l0: &ast::PolyLagrange<Rt>,
    l_last: &ast::PolyLagrange<Rt>,
    l_active_row: &ast::PolyLagrange<Rt>,
    extended_omega_powers: &ast::PolyLagrange<Rt>,
    beta: &ast::Scalar<Rt>,
    gamma: &ast::Scalar<Rt>,
    y: &ast::Scalar<Rt>,
    beta_mul_zeta: &ast::Scalar<Rt>,
    delta: &ast::Scalar<Rt>,
    theta: &ast::Scalar<Rt>,
) where
    Rt::Field: WithSmallOrderMulGroup<3>,
{
    let domain = &pk.vk.domain;
    let rot_scale = 1 << (domain.extended_k() - domain.k());
    let extended_n = domain.extended_len() as u64;

    let mut add_constraint = |p: ast::PolyLagrange<Rt>| {
        *h = h.clone() * y.clone() + p;
    };

    // Custom gates
    pk.vk
        .cs
        .gates()
        .iter()
        .flat_map(|gate| {
            gate.polynomials().iter().map(|expr| {
                evaluate_expression::<_, true>(expr, table, challenges, rot_scale).unwrap_poly()
            })
        })
        .for_each(|p| add_constraint(p));

    // Premutation constraints
    if !permutation_ppps.is_empty() {
        let blinding_factors = pk.vk.cs.blinding_factors();
        let last_rotation = -((blinding_factors + 1) as i32);

        let chunk_len = pk.vk.cs_degree - 2;
        let permutation_ppps: Vec<_> = permutation_ppps
            .iter()
            .map(|p| p.to_coef())
            .map(|p| coef_to_extended(&p, extended_n, zetas))
            .collect();
        add_constraint(
            (ast::Scalar::one() - permutation_ppps.first().unwrap().clone()) * l0.clone(),
        );
        let last = permutation_ppps.last().unwrap().clone();
        add_constraint((last.clone() * last.clone() - last.clone()) * l_last.clone());

        for (i, ppp) in permutation_ppps.iter().skip(1).enumerate() {
            add_constraint(
                (ppp.clone() - permutation_ppps[i - 1].rotate(rot_scale * last_rotation))
                    * l0.clone(),
            );
        }

        let mut delta_power = beta_mul_zeta.clone();
        for ((columns, perm_exts), ppp) in pk
            .vk
            .cs
            .permutation
            .columns
            .chunks(chunk_len)
            .zip(pk_permutation_exts.chunks(chunk_len))
            .zip(permutation_ppps.iter())
        {
            let mut left = ppp.rotate(rot_scale);
            for (perm_ext, col) in perm_exts.iter().zip(columns) {
                let col_values = table.ext(*col);
                left = left * (col_values + beta.clone() * perm_ext.clone() + gamma.clone());
            }

            let mut right = ppp.clone();
            for col in columns {
                let col_values = table.ext(*col);
                right = right
                    * (col_values
                        + delta_power.clone() * extended_omega_powers.clone()
                        + gamma.clone());
                delta_power = delta_power * delta.clone();
            }

            add_constraint((left - right) * l_active_row.clone());
        }
    }

    for ((ppa, ppp), pa) in plas.iter().zip(lookup_ppp_coefs.iter()).zip(las.iter()) {
        let ppp_ext = coef_to_extended(ppp, extended_n, zetas);
        let pi_ext = coef_to_extended(&ppa.pi_coef, extended_n, zetas);
        let pt_ext = coef_to_extended(&ppa.pt_coef, extended_n, zetas);

        let inputs_evaluated = pa
            .input_expressions
            .iter()
            .map(|expr| {
                evaluate_expression::<_, true>(expr, table, challenges, rot_scale).unwrap_poly()
            })
            .collect::<Vec<_>>();
        let tables_evaluated = pa
            .table_expressions
            .iter()
            .map(|expr| {
                evaluate_expression::<_, true>(expr, table, challenges, rot_scale).unwrap_poly()
            })
            .collect::<Vec<_>>();
        let ci_ext = compress_expressions(inputs_evaluated.iter().cloned(), theta, extended_n);
        let ct_ext = compress_expressions(tables_evaluated.iter().cloned(), theta, extended_n);

        let t = (ct_ext + gamma.clone()) * (ci_ext + beta.clone());

        add_constraint((ast::Scalar::one() - ppp_ext.clone()) * l0.clone());
        add_constraint((ppp_ext.clone() * ppp_ext.clone() - ppp_ext.clone()) * l_last.clone());

        add_constraint(
            (ppp_ext.rotate(rot_scale) * (pi_ext + beta.clone()) * (pt_ext + gamma.clone())
                - ppp_ext * t)
                * l_active_row.clone(),
        );
    }

    // Shuffle not implemented yet
}

fn construct_vanishing<Rt: RuntimeType>(
    h: &ast::PolyLagrange<Rt>,
    zetas_inv: &ast::PolyLagrange<Rt>,
    vanishing_divisor: &ast::PolyLagrange<Rt>,
    extended_truncted_n: u64,
    n: u64,
) -> Vec<ast::PolyCoef<Rt>> {
    let vanishing = h.clone() * vanishing_divisor.clone();
    let vanishing = extended_to_coef(&vanishing, extended_truncted_n, zetas_inv);
    let pieces = (0..extended_truncted_n)
        .step_by(n as usize)
        .map(|offset| vanishing.slice(offset, offset + n))
        .collect();
    pieces
}

fn evaluate_permutation<Rt: RuntimeType>(
    permutation_ppp_coefs: &[ast::PolyCoef<Rt>],
    x: &ast::Scalar<Rt>,
    transcript: &mut ast::Transcript<Rt>,
    pk: &ProvingKey<Rt::PointAffine>,
    get_x_mul_omega_power: &mut impl FnMut(i32) -> ast::Scalar<Rt>,
) {
    let blinding_facotrs = pk.vk.cs.blinding_factors();
    let mut iter = permutation_ppp_coefs.iter();

    while let Some(ppp) = iter.next() {
        let eval = ppp.evaluate(x);
        let eval_next = ppp.evaluate(&get_x_mul_omega_power(1));

        transcript.hash_scalar(&eval, HashTyp::WriteProof);
        transcript.hash_scalar(&eval_next, HashTyp::WriteProof);

        if iter.len() > 0 {
            let eval_last = ppp.evaluate(&get_x_mul_omega_power(-((blinding_facotrs + 1) as i32)));

            transcript.hash_scalar(&eval_last, HashTyp::WriteProof);
        }
    }
}

fn evaluate_lookup<Rt: RuntimeType>(
    ppp_coef: &ast::PolyCoef<Rt>,
    pla: &PermutedPlookupArgument<Rt>,
    x: &ast::Scalar<Rt>,
    transcript: &mut ast::Transcript<Rt>,
    get_x_mul_omega_power: &mut impl FnMut(i32) -> ast::Scalar<Rt>,
) {
    let ppp_eval = ppp_coef.evaluate(x);
    let ppp_eval_next = ppp_coef.evaluate(&get_x_mul_omega_power(1));
    let pi_eval = pla.pi_coef.evaluate(x);
    let pi_eval_prev = pla.pi_coef.evaluate(&get_x_mul_omega_power(-1));
    let pt_eval = pla.pt_coef.evaluate(x);

    [ppp_eval, ppp_eval_next, pi_eval, pi_eval_prev, pt_eval]
        .into_iter()
        .for_each(|p| transcript.hash_scalar(&p, HashTyp::WriteProof));
}

fn coef_to_extended<Rt: RuntimeType>(
    coefs: &ast::PolyCoef<Rt>,
    extended_n: u64,
    zetas: &ast::PolyLagrange<Rt>,
) -> ast::PolyLagrange<Rt> {
    let coefs = coefs.distribute_powers(zetas);
    let extended = coefs.extend(extended_n);
    extended.to_lagrange()
}

fn extended_to_coef<Rt: RuntimeType>(
    values: &ast::PolyLagrange<Rt>,
    len: u64,
    zetas_inv: &ast::PolyLagrange<Rt>,
) -> ast::PolyCoef<Rt> {
    let extended_coef = values.to_coef();
    let extended_coef = extended_coef.distribute_powers(zetas_inv);
    extended_coef.slice(0, len)
}

fn kzg_commit_lagrange<Rt: RuntimeType>(
    poly: impl Iterator<Item = ast::PolyLagrange<Rt>>,
    points: &ast::PrecomputedPoints<Rt>,
    transcript: &mut ast::Transcript<Rt>,
) {
    let points = ast::point::msm_lagrange(poly, points);
    points.iter().for_each(|point| {
        transcript.hash_point(&point, HashTyp::WriteProof);
    })
}

fn kzg_commit_coef<Rt: RuntimeType>(
    poly: impl Iterator<Item = ast::PolyCoef<Rt>>,
    points: &ast::PrecomputedPoints<Rt>,
    transcript: &mut ast::Transcript<Rt>,
) {
    let points = ast::point::msm_coef(poly, points);
    points.iter().for_each(|point| {
        transcript.hash_point(&point, HashTyp::WriteProof);
    })
}

struct Table<Rt: RuntimeType> {
    instance_values: Vec<ast::PolyLagrange<Rt>>,
    instance_coefs: Vec<ast::PolyCoef<Rt>>,
    instance_exts: Vec<ast::PolyLagrange<Rt>>,
    advice_values: Vec<ast::PolyLagrange<Rt>>,
    advice_coefs: Vec<ast::PolyCoef<Rt>>,
    advice_exts: Vec<ast::PolyLagrange<Rt>>,
    fixed_values: Vec<ast::PolyLagrange<Rt>>,
    fixed_coefs: Vec<ast::PolyCoef<Rt>>,
    fixed_exts: Vec<ast::PolyLagrange<Rt>>,
}

impl<Rt: RuntimeType> Table<Rt> {
    pub fn lagrange(&self, col: Column<Any>) -> ast::PolyLagrange<Rt> {
        match col.column_type() {
            Any::Instance => self.instance_values[col.index()].clone(),
            Any::Advice(..) => self.advice_values[col.index()].clone(),
            Any::Fixed => self.fixed_values[col.index()].clone(),
        }
    }
    pub fn ext(&self, col: Column<Any>) -> ast::PolyLagrange<Rt> {
        match col.column_type() {
            Any::Instance => self.instance_exts[col.index()].clone(),
            Any::Advice(..) => self.advice_exts[col.index()].clone(),
            Any::Fixed => self.fixed_exts[col.index()].clone(),
        }
    }
}

struct ProverQuery<Rt: RuntimeType> {
    rotation: i32,
    poly: ast::PolyCoef<Rt>,
}

fn open_permutation<'a, Rt: RuntimeType>(
    ppps: &'a [ast::PolyCoef<Rt>],
    pk: &ProvingKey<Rt::PointAffine>,
) -> impl Iterator<Item = ProverQuery<Rt>> + 'a {
    let blinding_facotrs = pk.vk.cs.blinding_factors();

    ppps.iter()
        .flat_map(move |ppp| {
            [
                ProverQuery {
                    rotation: 0,
                    poly: ppp.clone(),
                },
                ProverQuery {
                    rotation: 1,
                    poly: ppp.clone(),
                },
            ]
            .into_iter()
        })
        .chain(ppps.iter().rev().skip(1).flat_map(move |ppp| {
            Some(ProverQuery {
                rotation: -((blinding_facotrs + 1) as i32),
                poly: ppp.clone(),
            })
        }))
}

fn open_permutation_indices<'a, Rt: RuntimeType>(
    pk_permutation_coefs: &'a [ast::PolyCoef<Rt>],
) -> impl Iterator<Item = ProverQuery<Rt>> + 'a {
    pk_permutation_coefs
        .iter()
        .cloned()
        .map(move |p| ProverQuery {
            rotation: 0,
            poly: p,
        })
}

fn open_lookup<Rt: RuntimeType>(
    pla: &PermutedPlookupArgument<Rt>,
    ppp: &ast::PolyCoef<Rt>,
) -> impl Iterator<Item = ProverQuery<Rt>> {
    [
        ProverQuery {
            rotation: 0,
            poly: ppp.clone(),
        },
        ProverQuery {
            rotation: 0,
            poly: pla.pi_coef.clone(),
        },
        ProverQuery {
            rotation: 0,
            poly: pla.pt_coef.clone(),
        },
        ProverQuery {
            rotation: -1,
            poly: pla.pi_coef.clone(),
        },
        ProverQuery {
            rotation: 1,
            poly: ppp.clone(),
        },
    ]
    .into_iter()
}

struct RotationSet<Rt: RuntimeType, P> {
    points: P,
    commitments: Vec<ast::PolyCoef<Rt>>,
}

fn construct_intermediate_sets<Rt: RuntimeType>(
    queries: impl Iterator<Item = ProverQuery<Rt>>,
) -> (BTreeSet<i32>, Vec<RotationSet<Rt, BTreeSet<i32>>>) {
    let queries = queries.collect::<Vec<_>>();

    // All points that appear in queries
    let mut super_point_set = BTreeSet::new();

    // Collect rotation sets for each commitment
    // Example elements in the vector:
    // (C_0, {r_5}),
    // (C_1, {r_1, r_2, r_3}),
    // (C_2, {r_2, r_3, r_4}),
    // (C_3, {r_2, r_3, r_4}),
    // ...
    let mut commitment_rotation_set_map: Vec<(ast::PolyCoef<Rt>, BTreeSet<i32>)> = vec![];
    for query in queries.iter() {
        let rotation = query.rotation;
        super_point_set.insert(rotation);
        if let Some(commitment_rotation_set) = commitment_rotation_set_map
            .iter_mut()
            .find(|(commitment, _)| commitment.is(&query.poly))
        {
            let (_, rotation_set) = commitment_rotation_set;
            rotation_set.insert(rotation);
        } else {
            commitment_rotation_set_map.push((
                query.poly.clone(),
                BTreeSet::from_iter(std::iter::once(rotation)),
            ));
        };
    }

    // Flatten rotation sets and collect commitments that opens against each commitment set
    // Example elements in the vector:
    // {r_5}: [C_0],
    // {r_1, r_2, r_3} : [C_1]
    // {r_2, r_3, r_4} : [C_2, C_3],
    // ...
    // NOTE: we want to make the order of the collection of rotation sets independent of the opening points, to ease the verifier computation
    let mut rotation_set_commitment_map: Vec<RotationSet<Rt, BTreeSet<i32>>> = vec![];
    for (commitment, rotation_set) in commitment_rotation_set_map.into_iter() {
        if let Some(rotation_set_commitment) = rotation_set_commitment_map
            .iter_mut()
            .find(|rs| rs.points == rotation_set)
        {
            rotation_set_commitment.commitments.push(commitment);
        } else {
            rotation_set_commitment_map.push(RotationSet {
                points: rotation_set,
                commitments: vec![commitment],
            });
        };
    }
    (super_point_set, rotation_set_commitment_map)
}

fn div_by_vanishing<'a, Rt: RuntimeType>(
    p: ast::PolyCoef<Rt>,
    roots: impl Iterator<Item = &'a ast::Scalar<Rt>>,
) -> ast::PolyCoef<Rt> {
    roots.fold(p, |p, b| p.kate_div(b))
}

fn shplonk_commit<Rt: RuntimeType>(
    queries: impl Iterator<Item = ProverQuery<Rt>>,
    transcript: &mut ast::Transcript<Rt>,
    get_x_mul_omega_power: &mut impl FnMut(i32) -> ast::Scalar<Rt>,
    coef_points: &ast::PrecomputedPoints<Rt>,
    evaluate_vanishing_polynomail_f: user_functions::EvaluateVanishingPolynomailF<Rt>,
    n: u64,
) {
    let y = transcript.squeeze_challenge_scalar();
    let (super_point_set, rotation_sets) = construct_intermediate_sets(queries);

    let points_complement: Vec<Vec<_>> = rotation_sets
        .iter()
        .map(|RotationSet { points, .. }| {
            let com = super_point_set.difference(points);
            com.into_iter()
                .map(|rot| get_x_mul_omega_power(*rot))
                .collect()
        })
        .collect();

    let rotation_sets: Vec<RotationSet<Rt, Vec<ast::Scalar<Rt>>>> = rotation_sets
        .into_iter()
        .map(
            |RotationSet {
                 points,
                 commitments,
             }| RotationSet {
                points: points
                    .into_iter()
                    .map(|rot| get_x_mul_omega_power(rot))
                    .collect(),
                commitments,
            },
        )
        .collect();

    let rs: Vec<Vec<_>> = rotation_sets
        .iter()
        .map(
            |RotationSet {
                 points,
                 commitments,
             }| {
                commitments
                    .iter()
                    .map(|poly| {
                        let ys: Vec<_> = points.iter().map(|x| poly.evaluate(x)).collect();
                        ast::PolyCoef::interplote(points.clone(), ys)
                    })
                    .collect()
            },
        )
        .collect();

    let v = transcript.squeeze_challenge_scalar();

    let his = rotation_sets.iter().zip(rs.iter()).map(|(rot_set, rs)| {
        let numerator = rot_set
            .commitments
            .iter()
            .rev()
            .zip(rs.iter().rev())
            .fold(ast::PolyCoef::zero(n), |acc, (f, r)| {
                acc * y.clone() + f.clone() - r.clone()
            });
        div_by_vanishing(numerator, rot_set.points.iter())
    });

    let h = his
        .into_iter()
        .rev()
        .fold(ast::PolyCoef::zero(n), |acc, hi| acc * v.clone() + hi);
    kzg_commit_coef(std::iter::once(h.clone()), coef_points, transcript);

    let u = transcript.squeeze_challenge_scalar();

    let lis = rotation_sets
        .iter()
        .zip(rs.iter())
        .zip(points_complement.into_iter())
        .map(|((rot_set, rs), complement_points)| {
            let factor1 = rot_set
                .commitments
                .iter()
                .rev()
                .zip(rs.iter().rev())
                .fold(ast::PolyCoef::zero(n), |acc, (f, r)| {
                    acc * y.clone() + f.clone() - r.evaluate(&u)
                });
            let factor2 = evaluate_vanishing_polynomail_f.call(
                ast::Array::construct(complement_points.into_iter()),
                u.clone(),
            );
            factor1 * factor2
        });

    let l_left = lis
        .rev()
        .fold(ast::PolyCoef::zero(n), |acc, li| acc * v.clone() + li);
    let l_right = h * evaluate_vanishing_polynomail_f.call(
        ast::Array::construct(
            super_point_set
                .iter()
                .map(|rot| get_x_mul_omega_power(*rot)),
        ),
        u.clone(),
    );
    let l = l_left - l_right;

    let h1 = l.kate_div(&u);
    let alpha = h1.index(0).invert();
    let h1 = h1 * alpha;
    kzg_commit_coef(std::iter::once(h1), coef_points, transcript);
}

/// A pack of types for the runtime
pub struct RtInstance<Scheme, E, T>(PhantomData<(Scheme, E, T)>);

impl<Scheme, E, T> std::fmt::Debug for RtInstance<Scheme, E, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "RtInstance")
    }
}

impl<Scheme, E, T> Clone for RtInstance<Scheme, E, T> {
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

unsafe impl<Scheme, E, T> Send for RtInstance<Scheme, E, T> {}
unsafe impl<Scheme, E, T> Sync for RtInstance<Scheme, E, T> {}

impl<Scheme: CommitmentScheme + 'static, E, T> RuntimeType for RtInstance<Scheme, E, T>
where
    E: zkpoly_runtime::transcript::EncodedChallenge<Scheme::Curve> + 'static,
    T: zkpoly_runtime::transcript::TranscriptWrite<Scheme::Curve, E> + 'static,
    Scheme::Scalar: PrimeField,
{
    type Field = Scheme::Scalar;
    type PointAffine = Scheme::Curve;
    type Challenge = E;
    type Trans = T;
}

/// Shape of inputs of the computation graph
#[derive(Debug, Clone)]
pub struct InputsShape {
    n_circuits: usize,
    n_columns: usize,
    n: u64,
}

/// The generator for [`super::create_proof`].
pub fn create_proof<
    'params,
    Scheme: CommitmentScheme + 'static,
    P: Prover<'params, Scheme>,
    E: zkpoly_runtime::transcript::EncodedChallenge<Scheme::Curve> + 'static,
    T: zkpoly_runtime::transcript::TranscriptWrite<Scheme::Curve, E> + 'static,
    ConcreteCircuit: Circuit<Scheme::Scalar> + 'static + Send + Sync,
>(
    params: &Scheme::ParamsProver,
    pk: &ProvingKey<Scheme::Curve>,
    circuits: Vec<ConcreteCircuit>,
    allocator: &mut zkpoly_memory_pool::PinnedMemoryPool,
) -> (ast::Transcript<RtInstance<Scheme, E, T>>, InputsShape)
where
    Scheme::Scalar: WithSmallOrderMulGroup<3> + FromUniformBytes<64> + Ord,
    ConcreteCircuit::Config: 'static + Send + Sync,
{
    let domain = &pk.vk.domain;
    let extended_n: u64 = 2u64.pow(domain.extended_k());
    let mut meta = ConstraintSystem::default();
    #[cfg(feature = "circuit-params")]
    let config = ConcreteCircuit::configure_with_params(&mut meta, circuits[0].params());
    #[cfg(not(feature = "circuit-params"))]
    let config = ConcreteCircuit::configure(&mut meta);

    let meta = &pk.vk.cs;

    assert!(P::QUERY_INSTANCE == false);

    let mut entry_definer = ast::EntryDefiner::new();

    // Compute constants

    let extended_omega_powers = {
        let mut power = Scheme::Scalar::ONE;
        ast::PolyLagrange::constant_from_iter(
            (0..extended_n).map(|_| {
                let r = power;
                power = power * domain.get_extended_omega();
                r
            }),
            extended_n,
            allocator,
        )
    };
    let zetas = ast::PolyLagrange::constant(
        &vec![
            Scheme::Scalar::ONE,
            domain.get_g_coset().clone(),
            domain.get_g_coset_inv().clone(),
        ],
        allocator,
    );
    let zeta = ast::Scalar::constant(Scheme::Scalar::ZETA);
    let extended_truncted_n = domain.n() * domain.get_quotient_poly_degree() as u64;
    let zetas_inv = ast::PolyLagrange::constant(
        &vec![
            Scheme::Scalar::ONE,
            domain.get_g_coset_inv().clone(),
            domain.get_g_coset().clone(),
        ],
        allocator,
    );

    let omega = ast::Scalar::constant(domain.get_omega());
    let omega_inv = ast::Scalar::constant(domain.get_omega_inv());
    let omega_powers = {
        let mut power = Scheme::Scalar::ONE;
        ast::PolyLagrange::constant_from_iter(
            (0..domain.n()).map(|_| {
                let r = power;
                power = power * domain.get_omega();
                r
            }),
            domain.n(),
            allocator,
        )
    };
    let delta = ast::Scalar::constant(Scheme::Scalar::DELTA);

    let lagrange_points = ast::PrecomputedPoints::construct(params.lagrange_points(), allocator);
    let coef_points = ast::PrecomputedPoints::construct(params.coef_points(), allocator);

    let l0 = ast::PolyLagrange::constant(&pk.l0.values, allocator);
    let l_last = ast::PolyLagrange::constant(&pk.l_last.values, allocator);
    let l_active_row = ast::PolyLagrange::constant(&pk.l_active_row.values, allocator);

    let vanishing_divisor = {
        let tlen = domain.get_t_evaluations().len() as u64;
        ast::PolyLagrange::constant_from_iter(
            (0..extended_n).map(|i| domain.get_t_evaluations()[(i % tlen) as usize]),
            extended_n,
            allocator,
        )
    };

    // Declare inputs
    let inputs_shape = InputsShape {
        n_circuits: circuits.len(),
        n_columns: pk.vk.cs.num_instance_columns,
        n: params.n(),
    };

    let instances: Vec<Vec<ast::PolyLagrange<RtInstance<Scheme, E, T>>>> = (0..circuits.len())
        .map(|i| {
            (0..pk.vk.cs.num_instance_columns)
                .map(|j| {
                    entry_definer.define(
                        format!("instance_{}_{}", i, j),
                        type2::Typ::lagrange(params.n()),
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let mut transcript: ast::Transcript<RtInstance<Scheme, E, T>> =
        entry_definer.define("transcript".to_string(), type2::Typ::Transcript);

    let fixed_values: Vec<_> = pk
        .fixed_values
        .iter()
        .map(|p| ast::PolyLagrange::constant(&p.values, allocator))
        .collect();

    let fixed_coefs: Vec<_> = pk
        .fixed_polys
        .iter()
        .map(|p| ast::PolyCoef::constant(&p.values, allocator))
        .collect();

    let fixed_exts: Vec<_> = pk
        .fixed_cosets
        .iter()
        .map(|p| ast::PolyLagrange::constant(&p.values, allocator))
        .collect();

    // Hash verfication key into transcript
    let vk_scalar = ast::Scalar::constant(pk.vk.transcript_repr.clone());
    transcript.hash_scalar(&vk_scalar, HashTyp::NoWriteProof);

    let mut advices: Vec<Vec<Option<_>>> =
        vec![vec![None; meta.num_advice_columns]; instances.len()];
    let new_hash_dict_f = user_functions::new_hash_dict();
    let mut challenges = new_hash_dict_f.call();

    let circuits = circuits
        .into_iter()
        .enumerate()
        .map(|(i, circuit)| ast::Whatever::constant(circuit, "circuit".to_string()))
        .collect::<Vec<_>>();

    let unusable_rows_start = params.n() as usize - (meta.blinding_factors() + 1);
    for current_phase in pk.vk.cs.phases() {
        let column_indices = meta
            .advice_column_phase
            .iter()
            .enumerate()
            .filter_map(|(column_index, phase)| {
                if current_phase == *phase {
                    Some(column_index)
                } else {
                    None
                }
            })
            .collect::<BTreeSet<_>>();

        for (i, ((circuit, advice), instance_values)) in circuits
            .iter()
            .zip(advices.iter_mut())
            .zip(instances.iter())
            .enumerate()
        {
            let calculate_advice_f = user_functions::calculate_advices::<_, ConcreteCircuit>(
                params.n(),
                params.k(),
                current_phase,
                meta,
                config.clone(),
            );
            let advices_numerator_dominators = calculate_advice_f.call(
                ast::Array::construct(instance_values.iter().cloned()),
                challenges.clone(),
                circuit.clone(),
            );

            let advice_numerators: Vec<_> = advices_numerator_dominators
                .iter()
                .take(meta.num_advice_columns)
                .enumerate()
                .filter(|(i, _)| column_indices.contains(i))
                .map(|(_, x)| x)
                .collect();
            let advice_dominators: Vec<_> = advices_numerator_dominators
                .iter()
                .skip(meta.num_advice_columns)
                .enumerate()
                .filter(|(i, _)| column_indices.contains(i))
                .map(|(_, x)| x)
                .collect();

            let advice_values: Vec<_> = advice_numerators
                .iter()
                .zip(advice_dominators.iter())
                .map(|(advice_numerator, advice_dominator)| {
                    advice_numerator.clone() / advice_dominator.clone()
                })
                .collect();

            let advice_values_blinded: Vec<_> = column_indices
                .iter()
                .zip(advice_values.iter())
                .map(|(j, advice_value)| {
                    if meta.unblinded_advice_columns.contains(j) {
                        advice_value.clone()
                    } else {
                        advice_value.blind(unusable_rows_start as u64, params.n())
                    }
                })
                .collect();

            kzg_commit_lagrange(
                advice_values_blinded.into_iter(),
                &lagrange_points,
                &mut transcript,
            );

            for (&i, p) in column_indices.iter().zip(advice_values.into_iter()) {
                advice[i] = Some(p);
            }
        }

        for (index, phase) in meta.challenge_phase.iter().enumerate() {
            if current_phase == *phase {
                let challenge_scalar = transcript.squeeze_challenge_scalar();

                let challenges_dict_insert_f = user_functions::hash_dict_insert(index);
                challenges = challenges_dict_insert_f.call(challenges, challenge_scalar);
            }
        }
    }

    let advices = advices
        .into_iter()
        .map(|advice| advice.into_iter().map(Option::unwrap).collect::<Vec<_>>())
        .collect::<Vec<_>>();
    let collect_challenges_f = user_functions::collect_challenges(meta.num_challenges);
    let challenges = collect_challenges_f.call(challenges);
    let challenges: Vec<_> = challenges.iter().collect();

    let tables = instances
        .into_iter()
        .zip(advices.into_iter())
        .enumerate()
        .map(|(i, (instance, advice))| {
            let instance_coefs: Vec<_> = instance.iter().map(|p| p.to_coef()).collect();
            let instance_exts: Vec<_> = instance_coefs
                .iter()
                .map(|p| coef_to_extended(p, extended_n, &zetas))
                .collect();
            let advice_coefs: Vec<_> = advice.iter().map(|p| p.to_coef()).collect();
            let advice_exts: Vec<_> = advice_coefs
                .iter()
                .map(|p| coef_to_extended(p, extended_n, &zetas))
                .collect();
            Table {
                instance_values: instance,
                instance_coefs,
                instance_exts,
                advice_values: advice,
                advice_coefs,
                advice_exts,
                fixed_coefs: fixed_coefs.clone(),
                fixed_values: fixed_values.clone(),
                fixed_exts: fixed_exts.clone(),
            }
        })
        .collect::<Vec<_>>();

    let theta = transcript.squeeze_challenge_scalar();

    let permute_expression_pair_f =
        user_functions::permute_expression_pair(meta.blinding_factors(), params.n());

    let lookup_permuteds: Vec<Vec<_>> = tables
        .iter()
        .map(|table| {
            pk.vk
                .cs
                .lookups
                .iter()
                .map(|argument| {
                    compute_permuted_for_plookup(
                        argument,
                        &theta,
                        table,
                        &challenges,
                        params.n(),
                        unusable_rows_start as u64,
                        &permute_expression_pair_f,
                    )
                })
                .collect()
        })
        .collect();
    kzg_commit_lagrange(
        lookup_permuteds
            .iter()
            .map(|ppas| {
                ppas.iter()
                    .map(|ppa| [ppa.pi_values.clone(), ppa.pt_values.clone()].into_iter())
                    .flatten()
            })
            .flatten(),
        &lagrange_points,
        &mut transcript,
    );

    let beta = transcript.squeeze_challenge_scalar();
    let gamma = transcript.squeeze_challenge_scalar();

    let pk_permutations: Vec<_> = pk
        .permutation
        .permutations
        .iter()
        .map(|p| ast::PolyLagrange::constant(&p.values, allocator))
        .collect();
    let permutation_ppps: Vec<_> = tables
        .iter()
        .map(|table| {
            let sets = compute_permutation_ppp(
                &pk.vk.cs.permutation.columns,
                pk,
                &pk_permutations,
                params.n(),
                table,
                &beta,
                &gamma,
                &omega_powers,
                &delta,
            );
            kzg_commit_lagrange(sets.iter().cloned(), &lagrange_points, &mut transcript);
            sets
        })
        .collect();

    let permutation_ppp_coefs: Vec<Vec<_>> = permutation_ppps
        .iter()
        .cloned()
        .map(|p| p.iter().map(ast::PolyLagrange::to_coef).collect())
        .collect();

    let plookup_ppps: Vec<Vec<_>> = lookup_permuteds
        .iter()
        .map(|ppas| {
            ppas.iter()
                .map(|ppa| {
                    compute_lookup_ppp(ppa, &beta, &gamma, unusable_rows_start as u64, params.n())
                })
                .collect()
        })
        .collect();

    kzg_commit_lagrange(
        plookup_ppps
            .iter()
            .map(|ppps| ppps.iter())
            .flatten()
            .cloned(),
        &lagrange_points,
        &mut transcript,
    );

    let plookup_ppp_coefs: Vec<Vec<_>> = plookup_ppps
        .iter()
        .cloned()
        .map(|p| p.iter().map(ast::PolyLagrange::to_coef).collect())
        .collect();

    // Shuffles are not used in zkevm-circuits, skipping here
    assert!(pk.vk.cs.shuffles.len() == 0);

    let random_poly = ast::PolyLagrange::random(params.n());
    let random_poly = random_poly.to_coef();
    kzg_commit_coef([random_poly].into_iter(), &coef_points, &mut transcript);

    let random_poly = ast::PolyLagrange::random(params.n());
    let random_poly = random_poly.to_coef();
    kzg_commit_coef(
        [random_poly.clone()].into_iter(),
        &coef_points,
        &mut transcript,
    );

    let y = transcript.squeeze_challenge_scalar();

    let pk_permutation_exts: Vec<_> = pk
        .permutation
        .cosets
        .iter()
        .map(|p| ast::PolyLagrange::constant(&p.values, allocator))
        .collect();

    let beta_mul_zeta = beta.clone() * zeta.clone();

    let mut h = ast::PolyLagrange::zeros(extended_n);
    tables
        .iter()
        .zip(permutation_ppps.iter())
        .zip(lookup_permuteds.iter())
        .zip(plookup_ppp_coefs.iter())
        .for_each(|(((table, permutation_ppps), plas), lookup_ppp_coefs)| {
            construct_primary_constraint(
                &mut h,
                &pk_permutation_exts,
                permutation_ppps,
                &pk.vk.cs.lookups,
                plas,
                lookup_ppp_coefs,
                table,
                pk,
                &challenges,
                &zetas,
                &l0,
                &l_last,
                &l_active_row,
                &extended_omega_powers,
                &beta,
                &gamma,
                &y,
                &beta_mul_zeta,
                &delta,
                &theta,
            );
        });

    let h_pieces = construct_vanishing(
        &h,
        &zetas_inv,
        &vanishing_divisor,
        extended_truncted_n,
        params.n(),
    );

    kzg_commit_coef(h_pieces.iter().cloned(), &coef_points, &mut transcript);

    let random_poly = ast::PolyLagrange::random(params.n());
    let random_poly = random_poly.to_coef();
    kzg_commit_coef(
        [random_poly.clone()].into_iter(),
        &coef_points,
        &mut transcript,
    );

    let x = transcript.squeeze_challenge_scalar();
    // for n < 2^30, this will do
    let xn = x.pow(params.n());

    assert!(P::QUERY_INSTANCE == false);

    let mut omega_powers = HashMap::new();
    let mut get_x_mul_omega_power = |power: i32| {
        omega_powers
            .entry(power)
            .or_insert_with(|| {
                if power > 0 {
                    x.clone() * omega.pow(power as u64)
                } else if power < 0 {
                    x.clone() * omega_inv.pow((-power) as u64)
                } else {
                    x.clone()
                }
            })
            .clone()
    };

    for table in tables.iter() {
        for (col, at) in meta.advice_queries.iter() {
            let point = get_x_mul_omega_power(at.0);
            let eval = table.advice_coefs[col.index()].evaluate(&point);
            transcript.hash_scalar(&eval, HashTyp::WriteProof);
        }
    }

    for (col, at) in meta.fixed_queries.iter() {
        let point = get_x_mul_omega_power(at.0);
        let eval = tables[0].fixed_coefs[col.index()].evaluate(&point);
        transcript.hash_scalar(&eval, HashTyp::WriteProof);
    }

    let h_collapsed = h_pieces
        .iter()
        .rev()
        .fold(ast::PolyCoef::zero(params.n()), |acc, piece| {
            acc * xn.clone() + piece.clone()
        });

    let random_eval = random_poly.evaluate(&x);
    transcript.hash_scalar(&random_eval, HashTyp::WriteProof);

    let pk_permutation_coefs: Vec<_> = pk
        .permutation
        .polys
        .iter()
        .map(|p| ast::PolyCoef::constant(&p.values, allocator))
        .collect();

    pk_permutation_coefs.iter().for_each(|p| {
        let eval = p.evaluate(&x);
        transcript.hash_scalar(&eval, HashTyp::WriteProof);
    });

    permutation_ppp_coefs.iter().for_each(|ppps| {
        evaluate_permutation(ppps, &x, &mut transcript, pk, &mut get_x_mul_omega_power);
    });

    lookup_permuteds
        .iter()
        .zip(plookup_ppp_coefs.iter())
        .for_each(|(plas, ppp_coefs)| {
            plas.iter().zip(ppp_coefs.iter()).for_each(|(pla, ppp)| {
                evaluate_lookup(ppp, pla, &x, &mut transcript, &mut get_x_mul_omega_power)
            });
        });
    // Skip shuffles here

    let instances = tables
        .iter()
        .zip(lookup_permuteds.iter())
        .zip(plookup_ppp_coefs.iter())
        .zip(permutation_ppp_coefs.iter())
        .flat_map(|(((table, plas), lookup_ppps), permutation_ppps)| {
            pk.vk
                .cs
                .advice_queries
                .iter()
                .map(|(column, at)| ProverQuery {
                    poly: table.advice_coefs[column.index()].clone(),
                    rotation: at.0,
                })
                .chain(open_permutation(permutation_ppps, pk))
                .chain(
                    plas.iter()
                        .zip(lookup_ppps.iter())
                        .flat_map(|(pla, ppp)| open_lookup(pla, ppp)),
                )
        })
        .chain(
            pk.vk
                .cs
                .fixed_queries
                .iter()
                .map(|(column, at)| ProverQuery {
                    rotation: at.0,
                    poly: tables[0].fixed_coefs[column.index()].clone(),
                }),
        )
        .chain(open_permutation_indices(&pk_permutation_coefs))
        .chain(
            [
                ProverQuery {
                    rotation: 0,
                    poly: h_collapsed,
                },
                ProverQuery {
                    rotation: 0,
                    poly: random_poly,
                },
            ]
            .into_iter(),
        );

    shplonk_commit(
        instances,
        &mut transcript,
        &mut get_x_mul_omega_power,
        &coef_points,
        user_functions::evaluate_vanishing_polynomial(),
        params.n(),
    );

    (transcript, inputs_shape)
}

impl InputsShape {
    /// Serialize the inputs to the entry table.
    pub fn serialize<Rt: RuntimeType>(
        &self,
        instances: Vec<Vec<rt::scalar::ScalarArray<Rt::Field>>>,
        transcript: Rt::Trans,
    ) -> rt::args::EntryTable<Rt> {
        assert!(instances.len() == self.n_circuits);
        instances.iter().for_each(|ins| {
            assert!(ins.len() == self.n_columns);
            ins.iter().for_each(|c| assert!(c.len() == self.n as usize))
        });

        let mut entry_table = rt::args::EntryTable::new();

        instances.into_iter().for_each(|instances| {
            instances.into_iter().for_each(|col| {
                rt::args::add_entry(&mut entry_table, rt::args::Variable::ScalarArray(col));
            });
        });

        rt::args::add_entry(
            &mut entry_table,
            rt::args::Variable::Transcript(zkpoly_runtime::transcript::TranscriptObject::new(
                transcript,
            )),
        );

        entry_table
    }
}
