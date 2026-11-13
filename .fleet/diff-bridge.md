# diff-bridge (fleet summary)

**Main result: the global different leaves T20 and T21 are proved.**
`ZInQKernel/Contrib/Different/Global.lean` proves
`ZInQ.Contrib.Different.hilbertDifferentFormula : GlueConductor.HilbertDifferentFormula` and
`ZInQ.Contrib.Different.serreDifferentBound : GlueConductor.SerreDifferentBound`, with exactly the
leaf types and no hypotheses. `#print axioms` gives [propext, Classical.choice, Quot.sound] for
both (VERIFIED). It also proves `ZInQ.Contrib.Different.D1_genuine_closed`, which is
`GlueConductor.D1_genuine` with both leaves applied (same axioms).

**Local leaves, importable.** `ZInQKernel/Contrib/Different/Local.lean` contains t-different's
proofs, built on I6Base's definitions:
`PkgI6.hilbertDifferentFormula : PkgI6.HilbertDifferentFormula`,
`PkgI6.differentBound : PkgI6.DifferentBound`,
`PkgI6.herbrandQuotient : PkgI6.HerbrandQuotient` and
`PkgI6.herbrandTransitivity : PkgI6.HerbrandTransitivity`. All use the standard three axioms
(VERIFIED).

**How.** The arithmetic is Tau Ceti's global Hilbert formula (`LocalGlobal/Different/Exponent.lean`)
and its global Serre bound (`LocalGlobal/Different/Wild.lean`). This task's bridge:
* `differentIdeal ℤ (𝓞 L) = differentIdeal (𝓞 ℚ) (𝓞 L)`;
* `P.ramificationIdx ℤ = P.ramificationIdx (𝓞 ℚ)`;
* Tau Ceti's `Ideal.ramificationGroup` is `GlueConductor.ramGroup` (both are `(P^(i+1)).inertia`);
* the passage from `multiplicity`/`finsum` to divisibility, and `v_P(e) = e·v_p(e)`.

**Compiles.** `lake build ZInQKernel.Contrib.Different.Local` and `lake build ZInQKernel.Contrib.Different.Global`
both succeed. The base is merged origin/wip/tc-port (f22bb604).

**Vendored by this task** (outside port1/kw-rest): 11 Tau Ceti oct16 modules in the closure of
`LocalGlobal/Different/Wild`, listed in `scratch/diff-bridge/wild-extra.txt`. They are unmodified
apart from tcport.py's import rewrite and provenance line.

**Remains.** Nothing for T20/T21. An integrator can fill `HSyn.TextbookLeaves.t20/t21/t22a/t22b`
and the `hH`/`hS` hypotheses of `D1_genuine`/`D1_local`/`D1_krasner` with these theorems.
Report: docs/research/diff-bridge.md. Log: scratch/diff-bridge/log.md.
