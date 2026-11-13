# diff-bridge (fleet summary)

**Main result: the global different leaves T20 and T21 are proved.** Each theorem has exactly the
leaf type from `Breaks.lean`, takes no hypotheses, and `#print axioms` gives
[propext, Classical.choice, Quot.sound] (VERIFIED):
* `ZInQ.Contrib.Different.hilbertDifferentFormula : GlueConductor.HilbertDifferentFormula`
  (`ZInQKernel/Contrib/Different/Bridge.lean`);
* `ZInQ.Contrib.Different.serreDifferentBound_of_local : GlueConductor.SerreDifferentBound`
  (`ZInQKernel/Contrib/Different/SerreLocal.lean`). This proof uses t-different's local bound on
  `ℤ_p ⊆ 𝒪_{L_w}`, transported to `𝓞 L`;
* `ZInQ.Contrib.Different.serreDifferentBound : GlueConductor.SerreDifferentBound`
  (`ZInQKernel/Contrib/Different/Global.lean`). This second proof uses Tau Ceti's `Wild.lean`;
* `D1_genuine_closed_of_local` and `D1_genuine_closed`: `GlueConductor.D1_genuine` with both
  leaves applied.

**Local leaves, importable.** `ZInQKernel/Contrib/Different/Local.lean` contains t-different's
proofs, built on I6Base's definitions:
`PkgI6.hilbertDifferentFormula`, `PkgI6.differentBound`, `PkgI6.herbrandQuotient` and
`PkgI6.herbrandTransitivity`, each with exactly its `PkgI6` type and the standard axioms.

**How.** T20 comes from Tau Ceti's global Hilbert formula (`LocalGlobal/Different/Exponent.lean`).
The bridge proved here:
* `differentIdeal ℤ (𝓞 L) = differentIdeal (𝓞 ℚ) (𝓞 L)`;
* `P.ramificationIdx ℤ = P.ramificationIdx (𝓞 ℚ)`;
* `ramGroup` is Tau Ceti's `Ideal.ramificationGroup` (both are `(P^(i+1)).inertia`);
* the passage from multiplicity/finsum to divisibility, and `v_P(e) = e·v_p(e)`;
* for the local route, `v·𝒪_v = 𝔪_v` and `e(𝔪_w/𝒪_v) = e(w/v)`.

**Compiles.** `lake build` succeeds for `ZInQKernel.Contrib.Different.{Local,Bridge,SerreLocal,Global}`
(base: merged origin/wip/tc-port f22bb604). `Bridge`, `Local` and `SerreLocal` need only tc-port's
port1 modules.

**Vendored by this task** (outside port1/kw-rest, needed only by `Global.lean`): 11 Tau Ceti oct16
modules in the closure of `LocalGlobal/Different/Wild`, listed in
`scratch/diff-bridge/wild-extra.txt` and unmodified. If they are unwanted, drop them together
with `Global.lean`.

**Remains.** Nothing for T20/T21. An integrator can fill `HSyn.TextbookLeaves.t20/t21/t22a/t22b`
and the `hH`/`hS` hypotheses of `D1_genuine`, `D1_local` and `D1_krasner`.
Report: docs/research/diff-bridge.md. Log: scratch/diff-bridge/log.md.
