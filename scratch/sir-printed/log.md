# sir-printed results log

## 2026-11-15 setup
- Base 9a100aa7. Build copied from ~/dzq-check2 (bc90deac, descendant of base; 17 files differ, none imported by
  ShimuraGoodReductionNoGuard).
- Field: `SGRSplit.ShimuraIntegralModelRep` (ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean l.94),
  consumed only by `openAddedLeaves16_of_OpenAddedLeaves17` (TailZ34) via
  `shimuraGoodReductionNoGuard_of_printed`. VERIFIED (grep).
- Uses of `hRep` inside `shimuraGoodReductionNoGuard_of_rep` (VERIFIED, read l.267-363): the universal property
  only at (i) `S = Spec ℚ̄` (injectivity: uniqueness; surjectivity: existence) and (ii) `S = 𝒴` for the objects
  `twistAb 𝒜 α`, `twistAb 𝒜 α⁻¹`, `rightMulAb 𝒜 u`, `rightMulAb 𝒜 u⁻¹` (existence) and `𝒜` (uniqueness, to make
  the two Hecke maps inverse).
- Downstream: `ShimuraGoodReductionNoGuard` → `ShimuraGoodReduction` (TailW) → `heckeVertWitness_of_leaves5`
  (TailN) → `HeckeVertWitness`, which needs every prime `p > 324` (TailL `heckeVertGauss_of_goodReduction`
  instantiates `hL p hp324` for each p). So no restriction of primes beyond `p > 324` is possible; p = 2, 3
  never occur. VERIFIED (read).
- Polarizations over a base: Mathlib v4.35 has none (no dual abelian scheme, no Picard scheme); the kernel has
  the vendored Jacobian-Challenge Picard presheaf `AlgebraicGeometry.picardFunctorNormalized` (rigidified
  relative Pic, any base) and t09-pic's field-level `T09Pic` defs (Pic representability, Pic⁰, φ_L, ē_n over a
  field). No polarization, dual abelian scheme or Weil pairing over a base. VERIFIED (grep).

## Lean step 1 (compiled)
- `ZInQKernel/Contrib/OneProof/ShimuraIntegralModelUsed.lean` (namespace `SIRPrinted`): new leaf
  `ShimuraIntegralModelUsed` (`ShimuraIntegralModelUsedAt p`: proper smooth `𝒴/ℤ_(p)`, `𝒜 : QMAbScheme 𝒴`,
  ∃! classifying point over `Spec ℚ̄` for every `QMAbScheme (Spec ℚ̄)`, and `𝒴 ≅ 𝒴` pulling `𝒜` back to
  `twistAb 𝒜 α` / `rightMulAb 𝒜 u`).
- `shimuraIntegralModelUsed_of_rep : ShimuraIntegralModelRep → ShimuraIntegralModelUsed` COMPILED.
- `shimuraGoodReductionNoGuard_of_used : ShimuraIntegralModelUsed → ShimuraGoodReductionNoGuard` COMPILED.
- `lake build ZInQKernel.Contrib.OneProof.ShimuraIntegralModelUsed` 88 s; axioms of both: propext,
  Classical.choice, Quot.sound (scratch/sir-printed/Check.lean). VERIFIED.
