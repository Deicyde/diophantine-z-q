# gauss-proof — fleet summary

**Verdict: DONE.** `theorem ZInQ.Contrib.functionalEquation5 : ZInQ.Literature.FunctionalEquation5`
is proved in Lean with no hypotheses (ZInQKernel/Contrib/GaussFE/FunctionalEquation5.lean).
`#print axioms` = [propext, Classical.choice, Quot.sound] (VERIFIED, scratch/gauss-proof/out_axioms.txt).

What compiles (each checked with `lake env lean` and `lake build`, no sorry):
- `Contrib/GaussFE/Gauss.lean` (Mathlib only): Gauss's count on y² = x³ − x for p ≡ 1 (mod 4),
  `gauss_jacobi`: #{y² = x³−x} = p + 2A with A + Bi = J(χ, χ²) (χ quartic, ℤ[i]-valued),
  A² + B² = p, −(A + Bi) ≡ 1 (mod 2+2i). The congruence uses the free involution t ↦ t⁻¹ on the
  Jacobi-sum summand in ℤ[i]/(2+2i). The norm comes from Mathlib's jacobiSum_mul_jacobiSum_inv.
- `Contrib/GaussFE/HeckeFE.lean`: bp-hecke-fe's HeckeFE.lean verbatim (namespace renamed only).
- `Contrib/GaussFE/FunctionalEquation5.lean`: `gaussPointCount : GaussPointCount` (the Prop copied
  verbatim), `literature_hecke_fe : HeckeContinuation5 ∧ FunctionalEquation5`, and the provider.
- `Contrib/GaussFE/Headline.lean`: FrozenTarget from SixContactMin + TYZThm35ReadingA + GrossZagier
  (and the variant with PropN.TYZInputs). HeckeContinuation and FunctionalEquation5 are no longer
  hypotheses of the headline. Standard axioms.

What remains: the provider `ZInQ.Contrib.heckeContinuation` (Literature.HeckeContinuation for every
d ≠ 0) is not closed. Only d ≡ 5 (mod 8) squarefree is proved, which is all the headline uses.
HeckeFE.lean duplicates bp-hecke-fe's scratch file; drop one copy at integration.
Report: docs/research/gauss-proof.md; log: scratch/gauss-proof/log.md.
