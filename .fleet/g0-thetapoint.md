# g0-thetapoint (fleet note)

**Result.** g0-split's missing piece 9, `ThetaPointOfFibre` (G19, F1 on `A`), is proved in Lean
from two strictly smaller named Props, with its statement unchanged:
`HSyn.G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios : FibreQMPeriod → ThetaRatiosAlgebraic →
ThetaPointOfFibre`.
* `FibreQMPeriod` (GLUE, large): some uniformization lattice of the fibre over `J(u)` is linearly
  isomorphic to bp-analytic's QM lattice `ι(𝒪)(τ,1)ᵀ`, with `jNum/jDen(Ω(τ)) = J(u)`. It needs
  R1(b) and the Hauptmodul comparison with `PkgI1.QMHauptmodul`.
* `ThetaRatiosAlgebraic` (LEAF candidate, composite; Shimura 1976 / Thomae, locators UNVERIFIED):
  at a period matrix of an abelian surface over a number field, the theta-constant ratios are
  algebraic.

A second route also compiles: `DimBaseChange` + `UniformizationExistsNF` (textbook) +
`FibreQMPeriodAll` + `ThetaNullAlgebraic`. `HSyn.glueOutputs_of_leaves_thetaParts` is g0-split's
main theorem with piece 9 replaced by the two Props. Verdict: the piece is true by model review
and not vacuous. Its height clause carries no theta content, because `z'` is not tied to `z`.

**Compiles (VERIFIED).** `lake env lean scratch/g0-thetapoint/ThetaPoint.lean` (g0-split's
`Split.lean` + one import of `ZInQKernel.HDecomp.Analytic.QMLattice` + `part_theta.lean`): 0
errors, no `sorry`, axioms `[propext, Classical.choice, Quot.sound]` (run8, 2m40s). New proved
glue:
* the F1 value passes to the number field (degree-0 homogeneity);
* `h(z') ≤ h(z)` (Mathlib `logHeight_comp_le`);
* the six odd theta constants vanish (`thetaConst_odd`);
* `Ω(τ)` is a Siegel period matrix of every lattice linearly isomorphic to `Λ_τ`;
* `PkgI1.Omega = BPAnalytic.QM.Omega`;
* algebraic ratios give a number-field point.

Numerics (`theta_check.py`):
* At `τ₋₂₄`: `j_θ = -16/27`, and the ratios `(θ_m/θ_{m₀})⁴` satisfy integer polynomials of
  degree 2 or 4.
* At `u = 1`: `τ_u` with `j_θ = J(1)` found. Algebraicity there is inconclusive.

**Remains.**
* `FibreQMPeriod`: next split is concrete R1(b) plus Möbius uniqueness, or Glazer's route R3 + R4
  + `f1_algebra` after refining `IsPeriodMatrix` to the canonical polarization.
* `ThetaRatiosAlgebraic`: human review of the citation.
* `UniformizationExistsNF`: transport from bp-analytic's leaf.

Report: `docs/research/g0-thetapoint.md`; log: `scratch/g0-thetapoint/log.md`.
