# elkies-coord (2026-11-15)

**Result.** The research field `elkiesX6StarPrinted` (gt-elkies; rated a consequence because its fibre clause was the
`ℚ̄`-point form of Elkies' "`t` is a coordinate on `X*(6) = X₆/W`") is discharged in Lean from one new leaf,
`HDec.QMSplit.Moduli.ElkiesCoord.ElkiesX6StarFunctionField`. The leaf is Elkies' statement in function-field form,
`ℚ(X₆)^W = ℚ(t)`, over Mathlib's `Scheme.functionField` with `W` acting by pullback (`ffPullback`, through
`stalkMap`). The CM values and the charts `s² = −t`, `r² = 3(t − 1)` are unchanged. Rated **printed form**, with
locators UNVERIFIED as before.

**What compiles (VERIFIED).**
* The proof is `ZInQKernel/Contrib/OneProof/ElkiesX6StarPrinted.lean` (~46 KB). It imports only
  `ZInQKernel.Contrib.OneProof.ElkiesX6Star`.
* The final theorem is `elkiesX6StarPrinted_of_functionField`. It uses standard axioms only.
* `#discharges` gives: `DISCHARGES [OpenResearchLeaves20.elkiesX6StarPrinted] … still assumes:
  [ElkiesCoord.ElkiesX6StarFunctionField]`, run against a freshly built `Main`.
* The autofold spec is `scratch/elkies-coord/autofold.json`. Its dry-run gives strict 47/11 → 48/10 and strictest
  46/12 → 47/11. The generated module compiles.
* How the proof goes:
  * every `g ∈ W` fixes `t`, so it acts on Elkies' coordinates by signs (germ calculus against the charts);
  * the automorphisms `s ↦ −s` and `r ↦ −r` of `ℚ(X₆)` fix `ℚ(t)`, so `ℚ(X₆)^W = ℚ(t)` forces elements of `W`
    negating `s`, `r` and `rs`;
  * the orbit relation is transitive (gt-elkies' `orbit_iff_twist`), so the orbits are the fibres of `t = −s²`.
* The integrality of `X₆` and the regularity of `t` at the generic point are also proved from the charts
  (Elkies' ring is a domain). The leaf therefore states its function-field clause under these hypotheses rather
  than asserting them.

**What remains.**
* The `0/∞` orientation and the display are unread (no network). The leaf needs a statement check against
  Elkies' paper and a `locators.md` row; a proposed row is in the report, §7.
* The converse (point form ⇒ function-field form) is not proved and not needed.
* Report: docs/research/elkies-coord.md.
