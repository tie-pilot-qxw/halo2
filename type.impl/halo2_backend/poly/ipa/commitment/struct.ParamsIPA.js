(function() {var type_impls = {
"halo2_backend":[["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Clone-for-ParamsIPA%3CC%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#25\">source</a><a href=\"#impl-Clone-for-ParamsIPA%3CC%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;C: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> + <a class=\"trait\" href=\"halo2_backend/arithmetic/trait.CurveAffine.html\" title=\"trait halo2_backend::arithmetic::CurveAffine\">CurveAffine</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html\" title=\"trait core::clone::Clone\">Clone</a> for <a class=\"struct\" href=\"halo2_backend/poly/ipa/commitment/struct.ParamsIPA.html\" title=\"struct halo2_backend::poly::ipa::commitment::ParamsIPA\">ParamsIPA</a>&lt;C&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#25\">source</a><a href=\"#method.clone\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\" class=\"fn\">clone</a>(&amp;self) -&gt; <a class=\"struct\" href=\"halo2_backend/poly/ipa/commitment/struct.ParamsIPA.html\" title=\"struct halo2_backend::poly::ipa::commitment::ParamsIPA\">ParamsIPA</a>&lt;C&gt;</h4></section></summary><div class='docblock'>Returns a copy of the value. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#tymethod.clone\">Read more</a></div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.clone_from\" class=\"method trait-impl\"><span class=\"rightside\"><span class=\"since\" title=\"Stable since Rust version 1.0.0\">1.0.0</span> · <a class=\"src\" href=\"https://doc.rust-lang.org/nightly/src/core/clone.rs.html#169\">source</a></span><a href=\"#method.clone_from\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\" class=\"fn\">clone_from</a>(&amp;mut self, source: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;Self</a>)</h4></section></summary><div class='docblock'>Performs copy-assignment from <code>source</code>. <a href=\"https://doc.rust-lang.org/nightly/core/clone/trait.Clone.html#method.clone_from\">Read more</a></div></details></div></details>","Clone","halo2_backend::poly::ipa::commitment::ParamsVerifierIPA"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Debug-for-ParamsIPA%3CC%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#25\">source</a><a href=\"#impl-Debug-for-ParamsIPA%3CC%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;C: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> + <a class=\"trait\" href=\"halo2_backend/arithmetic/trait.CurveAffine.html\" title=\"trait halo2_backend::arithmetic::CurveAffine\">CurveAffine</a>&gt; <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html\" title=\"trait core::fmt::Debug\">Debug</a> for <a class=\"struct\" href=\"halo2_backend/poly/ipa/commitment/struct.ParamsIPA.html\" title=\"struct halo2_backend::poly::ipa::commitment::ParamsIPA\">ParamsIPA</a>&lt;C&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.fmt\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#25\">source</a><a href=\"#method.fmt\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\" class=\"fn\">fmt</a>(&amp;self, f: &amp;mut <a class=\"struct\" href=\"https://doc.rust-lang.org/nightly/core/fmt/struct.Formatter.html\" title=\"struct core::fmt::Formatter\">Formatter</a>&lt;'_&gt;) -&gt; <a class=\"type\" href=\"https://doc.rust-lang.org/nightly/core/fmt/type.Result.html\" title=\"type core::fmt::Result\">Result</a></h4></section></summary><div class='docblock'>Formats the value using the given formatter. <a href=\"https://doc.rust-lang.org/nightly/core/fmt/trait.Debug.html#tymethod.fmt\">Read more</a></div></details></div></details>","Debug","halo2_backend::poly::ipa::commitment::ParamsVerifierIPA"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-Params%3CC%3E-for-ParamsIPA%3CC%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#71-148\">source</a><a href=\"#impl-Params%3CC%3E-for-ParamsIPA%3CC%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;C: <a class=\"trait\" href=\"halo2_backend/arithmetic/trait.CurveAffine.html\" title=\"trait halo2_backend::arithmetic::CurveAffine\">CurveAffine</a>&gt; <a class=\"trait\" href=\"halo2_backend/poly/commitment/trait.Params.html\" title=\"trait halo2_backend::poly::commitment::Params\">Params</a>&lt;C&gt; for <a class=\"struct\" href=\"halo2_backend/poly/ipa/commitment/struct.ParamsIPA.html\" title=\"struct halo2_backend::poly::ipa::commitment::ParamsIPA\">ParamsIPA</a>&lt;C&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.commit_lagrange\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#92-108\">source</a><a href=\"#method.commit_lagrange\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"halo2_backend/poly/commitment/trait.Params.html#tymethod.commit_lagrange\" class=\"fn\">commit_lagrange</a>(\n    &amp;self,\n    engine: &amp;impl MsmAccel&lt;C&gt;,\n    poly: &amp;<a class=\"struct\" href=\"halo2_backend/poly/struct.Polynomial.html\" title=\"struct halo2_backend::poly::Polynomial\">Polynomial</a>&lt;C::Scalar, <a class=\"struct\" href=\"halo2_backend/poly/struct.LagrangeCoeff.html\" title=\"struct halo2_backend::poly::LagrangeCoeff\">LagrangeCoeff</a>&gt;,\n    r: <a class=\"struct\" href=\"halo2_backend/poly/commitment/struct.Blind.html\" title=\"struct halo2_backend::poly::commitment::Blind\">Blind</a>&lt;C::Scalar&gt;\n) -&gt; C::Curve</h4></section></summary><div class=\"docblock\"><p>This commits to a polynomial using its evaluations over the $2^k$ size\nevaluation domain. The commitment will be blinded by the blinding factor\n<code>r</code>.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.write\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#111-123\">source</a><a href=\"#method.write\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"halo2_backend/poly/commitment/trait.Params.html#tymethod.write\" class=\"fn\">write</a>&lt;W: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/io/trait.Write.html\" title=\"trait std::io::Write\">Write</a>&gt;(&amp;self, writer: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut W</a>) -&gt; <a class=\"type\" href=\"https://doc.rust-lang.org/nightly/std/io/error/type.Result.html\" title=\"type std::io::error::Result\">Result</a>&lt;<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.unit.html\">()</a>&gt;</h4></section></summary><div class=\"docblock\"><p>Writes params to a buffer.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.read\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#126-147\">source</a><a href=\"#method.read\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"halo2_backend/poly/commitment/trait.Params.html#tymethod.read\" class=\"fn\">read</a>&lt;R: <a class=\"trait\" href=\"https://doc.rust-lang.org/nightly/std/io/trait.Read.html\" title=\"trait std::io::Read\">Read</a>&gt;(reader: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.reference.html\">&amp;mut R</a>) -&gt; <a class=\"type\" href=\"https://doc.rust-lang.org/nightly/std/io/error/type.Result.html\" title=\"type std::io::error::Result\">Result</a>&lt;Self&gt;</h4></section></summary><div class=\"docblock\"><p>Reads params from a buffer.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.k\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#72-74\">source</a><a href=\"#method.k\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"halo2_backend/poly/commitment/trait.Params.html#tymethod.k\" class=\"fn\">k</a>(&amp;self) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a></h4></section></summary><div class='docblock'>Logarithmic size of the circuit</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.n\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#76-78\">source</a><a href=\"#method.n\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"halo2_backend/poly/commitment/trait.Params.html#tymethod.n\" class=\"fn\">n</a>(&amp;self) -&gt; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a></h4></section></summary><div class='docblock'>Size of the circuit</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.downsize\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#80-87\">source</a><a href=\"#method.downsize\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"halo2_backend/poly/commitment/trait.Params.html#tymethod.downsize\" class=\"fn\">downsize</a>(&amp;mut self, k: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>)</h4></section></summary><div class='docblock'>Downsize <code>Params</code> with smaller <code>k</code>.</div></details></div></details>","Params<C>","halo2_backend::poly::ipa::commitment::ParamsVerifierIPA"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-ParamsProver%3CC%3E-for-ParamsIPA%3CC%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#150-233\">source</a><a href=\"#impl-ParamsProver%3CC%3E-for-ParamsIPA%3CC%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;C: <a class=\"trait\" href=\"halo2_backend/arithmetic/trait.CurveAffine.html\" title=\"trait halo2_backend::arithmetic::CurveAffine\">CurveAffine</a>&gt; <a class=\"trait\" href=\"halo2_backend/poly/commitment/trait.ParamsProver.html\" title=\"trait halo2_backend::poly::commitment::ParamsProver\">ParamsProver</a>&lt;C&gt; for <a class=\"struct\" href=\"halo2_backend/poly/ipa/commitment/struct.ParamsIPA.html\" title=\"struct halo2_backend::poly::ipa::commitment::ParamsIPA\">ParamsIPA</a>&lt;C&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle method-toggle\" open><summary><section id=\"method.new\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#153-211\">source</a><a href=\"#method.new\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"halo2_backend/poly/commitment/trait.ParamsProver.html#tymethod.new\" class=\"fn\">new</a>(k: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>) -&gt; Self</h4></section></summary><div class=\"docblock\"><p>Initializes parameters for the curve, given a random oracle to draw\npoints from.</p>\n</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.commit\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#216-232\">source</a><a href=\"#method.commit\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"halo2_backend/poly/commitment/trait.ParamsProver.html#tymethod.commit\" class=\"fn\">commit</a>(\n    &amp;self,\n    engine: &amp;impl MsmAccel&lt;C&gt;,\n    poly: &amp;<a class=\"struct\" href=\"halo2_backend/poly/struct.Polynomial.html\" title=\"struct halo2_backend::poly::Polynomial\">Polynomial</a>&lt;C::Scalar, <a class=\"struct\" href=\"halo2_backend/poly/struct.Coeff.html\" title=\"struct halo2_backend::poly::Coeff\">Coeff</a>&gt;,\n    r: <a class=\"struct\" href=\"halo2_backend/poly/commitment/struct.Blind.html\" title=\"struct halo2_backend::poly::commitment::Blind\">Blind</a>&lt;C::Scalar&gt;\n) -&gt; C::Curve</h4></section></summary><div class=\"docblock\"><p>This computes a commitment to a polynomial described by the provided\nslice of coefficients. The commitment will be blinded by the blinding\nfactor <code>r</code>.</p>\n</div></details></div></details>","ParamsProver<C>","halo2_backend::poly::ipa::commitment::ParamsVerifierIPA"],["<details class=\"toggle implementors-toggle\" open><summary><section id=\"impl-ParamsVerifier%3C'params,+C%3E-for-ParamsIPA%3CC%3E\" class=\"impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#60-69\">source</a><a href=\"#impl-ParamsVerifier%3C'params,+C%3E-for-ParamsIPA%3CC%3E\" class=\"anchor\">§</a><h3 class=\"code-header\">impl&lt;'params, C: <a class=\"trait\" href=\"halo2_backend/arithmetic/trait.CurveAffine.html\" title=\"trait halo2_backend::arithmetic::CurveAffine\">CurveAffine</a>&gt; <a class=\"trait\" href=\"halo2_backend/poly/commitment/trait.ParamsVerifier.html\" title=\"trait halo2_backend::poly::commitment::ParamsVerifier\">ParamsVerifier</a>&lt;'params, C&gt; for <a class=\"struct\" href=\"halo2_backend/poly/ipa/commitment/struct.ParamsIPA.html\" title=\"struct halo2_backend::poly::ipa::commitment::ParamsIPA\">ParamsIPA</a>&lt;C&gt;</h3></section></summary><div class=\"impl-items\"><details class=\"toggle\" open><summary><section id=\"associatedtype.MSM\" class=\"associatedtype trait-impl\"><a href=\"#associatedtype.MSM\" class=\"anchor\">§</a><h4 class=\"code-header\">type <a href=\"halo2_backend/poly/commitment/trait.ParamsVerifier.html#associatedtype.MSM\" class=\"associatedtype\">MSM</a> = <a class=\"struct\" href=\"halo2_backend/poly/ipa/msm/struct.MSMIPA.html\" title=\"struct halo2_backend::poly::ipa::msm::MSMIPA\">MSMIPA</a>&lt;'params, C&gt;</h4></section></summary><div class='docblock'>Multiscalar multiplication engine</div></details><details class=\"toggle\" open><summary><section id=\"associatedconstant.COMMIT_INSTANCE\" class=\"associatedconstant trait-impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#64\">source</a><a href=\"#associatedconstant.COMMIT_INSTANCE\" class=\"anchor\">§</a><h4 class=\"code-header\">const <a href=\"halo2_backend/poly/commitment/trait.ParamsVerifier.html#associatedconstant.COMMIT_INSTANCE\" class=\"constant\">COMMIT_INSTANCE</a>: <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.bool.html\">bool</a> = true</h4></section></summary><div class='docblock'>Can commit to instance or not.</div></details><details class=\"toggle method-toggle\" open><summary><section id=\"method.empty_msm\" class=\"method trait-impl\"><a class=\"src rightside\" href=\"src/halo2_backend/poly/ipa/commitment.rs.html#66-68\">source</a><a href=\"#method.empty_msm\" class=\"anchor\">§</a><h4 class=\"code-header\">fn <a href=\"halo2_backend/poly/commitment/trait.ParamsVerifier.html#tymethod.empty_msm\" class=\"fn\">empty_msm</a>(&amp;self) -&gt; <a class=\"struct\" href=\"halo2_backend/poly/ipa/msm/struct.MSMIPA.html\" title=\"struct halo2_backend::poly::ipa::msm::MSMIPA\">MSMIPA</a>&lt;'_, C&gt;</h4></section></summary><div class='docblock'>Generates an empty multiscalar multiplication struct using the\nappropriate params.</div></details></div></details>","ParamsVerifier<'params, C>","halo2_backend::poly::ipa::commitment::ParamsVerifierIPA"]]
};if (window.register_type_impls) {window.register_type_impls(type_impls);} else {window.pending_type_impls = type_impls;}})()