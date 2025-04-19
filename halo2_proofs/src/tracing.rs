//! Trace computation to debug correctness

use halo2curves::CurveAffine;

use crate::{
    plonk::{lookup, permutation},
    poly::{Coeff, ExtendedLagrangeCoeff, LagrangeCoeff, Polynomial},
};

/// Intermediate results of proof generation
#[derive(Clone, Debug, Default)]
pub struct Trace<C: CurveAffine> {
    /// circuit index |-> column index |-> polynomial
    pub(crate) instance_coefs: Vec<Vec<Polynomial<C::ScalarExt, Coeff>>>,
    pub(crate) instance_extended: Vec<Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>>>,
    /// phase index |-> circuit index |-> column index |-> polynomial
    pub(crate) advice_phases: Vec<Vec<Vec<Polynomial<C::ScalarExt, LagrangeCoeff>>>>,
    /// phase index |-> column index |-> point
    pub(crate) advice_commitments: Vec<Vec<C>>,
    pub(crate) challenges: Vec<C::ScalarExt>,
    /// circuit index |-> column index |-> polynomial
    pub(crate) advice_coefs: Vec<Vec<Polynomial<C::ScalarExt, Coeff>>>,
    pub(crate) advice_extended: Vec<Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>>>,
    /// circuit index |-> column index |-> polynomial
    pub(crate) advice_values: Vec<Vec<Polynomial<C::ScalarExt, LagrangeCoeff>>>,
    /// circuit index |-> lookup argument index |-> permuted lookup
    pub(crate) lookup_permuted: Vec<Vec<lookup::prover::Permuted<C>>>,
    pub(crate) theta: C::ScalarExt,
    pub(crate) beta: C::ScalarExt,
    pub(crate) gamma: C::ScalarExt,
    /// circuit index |-> permutation sets, which is vec of PPP's
    pub(crate) permutation_ppps: Vec<permutation::prover::Committed<C>>,
    /// circuit index |-> lookup argument index |-> PPP
    pub(crate) lookup_ppp: Vec<Vec<Polynomial<C::ScalarExt, LagrangeCoeff>>>,
    pub(crate) y: C::ScalarExt,
    /// circuit index |-> primary constraint polynomial after adding custom gates
    pub(crate) custom_gates_constraint: Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>>,
    /// circuit index |-> primary constraint polynomial after adding permutation PPP's
    pub(crate) permutation_constraint: Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>>,
    /// circuit index |-> primary constraint polynomial after adding lookup PPP's
    pub(crate) lookup_constraint: Vec<Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>>,
    pub(crate) vanished_h_extended: Polynomial<C::ScalarExt, ExtendedLagrangeCoeff>,
    pub(crate) vanished_h_coefs: Vec<C::ScalarExt>,
    /// pieces of vanished_h_coefs
    pub(crate) vanishing_pieces: Vec<Polynomial<C::ScalarExt, Coeff>>,
    pub(crate) vanishing_commitments: Vec<C>,
    pub(crate) x: C::ScalarExt,
    /// circuit index |-> column index |-> scalar
    pub(crate) advice_evals: Vec<Vec<C::ScalarExt>>,
    /// column index |-> scalar
    pub(crate) fixed_evals: Vec<C::ScalarExt>,
    /// Common permutation data
    pub(crate) common_permutation_evals: Vec<C::ScalarExt>,
    /// circuit index |-> permutation set index |-> vec of evaluated scalars
    pub(crate) permutation_evals: Vec<Vec<Vec<C::ScalarExt>>>,
    /// circuit index |-> lookup argument index |-> vec of evaluated scalars
    pub(crate) lookup_evals: Vec<Vec<Vec<C::ScalarExt>>>,
    pub(crate) shplonk_y: C::ScalarExt,
    pub(crate) shplonk_v: C::ScalarExt,
    /// rotation set index |-> commitment index |-> polynomial
    pub shplonk_fs: Vec<Vec<Polynomial<C::ScalarExt, Coeff>>>,
    /// rotation set index |-> commitment index |-> polynomial
    pub shplonk_rs: Vec<Vec<Polynomial<C::ScalarExt, Coeff>>>,
    /// rotation set index |-> commitment index |-> polynomial
    pub shplonk_f_minus_rs: Vec<Vec<Polynomial<C::ScalarExt, Coeff>>>,
    pub(crate) shplonk_lis: Vec<Polynomial<C::ScalarExt, Coeff>>,
    pub(crate) shplonk_r_evaluation_us: Vec<Vec<C::ScalarExt>>,
    pub(crate) shplonk_li_numerators: Vec<Vec<Polynomial<C::ScalarExt, Coeff>>>,
    pub(crate) shplonk_zis: Vec<C::ScalarExt>,
    pub(crate) shplonk_u: C::ScalarExt,
    pub(crate) shplonk_h: Polynomial<C::ScalarExt, Coeff>,
    pub(crate) shplonk_h1: Polynomial<C::ScalarExt, Coeff>,
}
