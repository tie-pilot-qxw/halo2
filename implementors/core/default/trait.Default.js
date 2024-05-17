(function() {var implementors = {
"halo2_backend":[["impl&lt;E: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> + Engine&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"halo2_backend/poly/kzg/msm/struct.MSMKZG.html\" title=\"struct halo2_backend::poly::kzg::msm::MSMKZG\">MSMKZG</a>&lt;E&gt;<span class=\"where fmt-newline\">where\n    E::G1Affine: <a class=\"trait\" href=\"halo2_backend/arithmetic/trait.CurveAffine.html\" title=\"trait halo2_backend::arithmetic::CurveAffine\">CurveAffine</a>&lt;ScalarExt = &lt;E as Engine&gt;::Fr, CurveExt = &lt;E as Engine&gt;::G1&gt;,\n    E::G1: <a class=\"trait\" href=\"halo2_backend/arithmetic/trait.CurveExt.html\" title=\"trait halo2_backend::arithmetic::CurveExt\">CurveExt</a>&lt;AffineExt = E::G1Affine&gt; + <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a>,\n    E::Fr: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a>,</span>"],["impl&lt;C: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> + <a class=\"trait\" href=\"halo2_backend/arithmetic/trait.CurveAffine.html\" title=\"trait halo2_backend::arithmetic::CurveAffine\">CurveAffine</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"halo2_backend/plonk/verifier/struct.BatchVerifier.html\" title=\"struct halo2_backend::plonk::verifier::BatchVerifier\">BatchVerifier</a>&lt;C&gt;"],["impl&lt;F: <a class=\"trait\" href=\"halo2_backend/arithmetic/trait.Field.html\" title=\"trait halo2_backend::arithmetic::Field\">Field</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"halo2_backend/poly/commitment/struct.Blind.html\" title=\"struct halo2_backend::poly::commitment::Blind\">Blind</a>&lt;F&gt;"]],
"halo2_frontend":[["impl&lt;F: Field&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"halo2_frontend/plonk/circuit/constraint_system/struct.ConstraintSystem.html\" title=\"struct halo2_frontend::plonk::circuit::constraint_system::ConstraintSystem\">ConstraintSystem</a>&lt;F&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"halo2_frontend/plonk/permutation/struct.Argument.html\" title=\"struct halo2_frontend::plonk::permutation::Argument\">Argument</a>"],["impl&lt;V&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"halo2_frontend/circuit/struct.Value.html\" title=\"struct halo2_frontend::circuit::Value\">Value</a>&lt;V&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"halo2_frontend/dev/struct.CircuitLayout.html\" title=\"struct halo2_frontend::dev::CircuitLayout\">CircuitLayout</a>"]],
"halo2_middleware":[["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"halo2_middleware/zal/impls/struct.H2cEngine.html\" title=\"struct halo2_middleware::zal::impls::H2cEngine\">H2cEngine</a>"],["impl&lt;C: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> + CurveAffine&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"halo2_middleware/zal/impls/struct.HasCurve.html\" title=\"struct halo2_middleware::zal::impls::HasCurve\">HasCurve</a>&lt;C&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"halo2_middleware/zal/impls/struct.NoCurve.html\" title=\"struct halo2_middleware::zal::impls::NoCurve\">NoCurve</a>"],["impl&lt;C: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a>, M: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"halo2_middleware/zal/impls/struct.PlonkEngineConfig.html\" title=\"struct halo2_middleware::zal::impls::PlonkEngineConfig\">PlonkEngineConfig</a>&lt;C, M&gt;"],["impl <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/default/trait.Default.html\" title=\"trait core::default::Default\">Default</a> for <a class=\"struct\" href=\"halo2_middleware/zal/impls/struct.NoMsmEngine.html\" title=\"struct halo2_middleware::zal::impls::NoMsmEngine\">NoMsmEngine</a>"]]
};if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()