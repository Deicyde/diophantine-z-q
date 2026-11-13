# ts-sn results log

## Step 0: setup (2026-11-13 09:16 PST)
- Base: origin/wip/prop-ts-glue merged (0ac06bd1). `scratch/ts-sn/TSSN.lean` starts as a verbatim
  copy of `scratch/prop-ts-glue/PropTSGlue.lean` (both target Props and their dependencies verbatim).
- Finding: `VerticalResidueSeparable` is already a theorem in that file:
  `verticalResidueSeparable_of_degree verticalResidueDegree` (prop-ts-glue step 13). Remaining
  target: `SNSpecialize`.

## Step 1: abstract criterion, compiled (scratch/ts-sn/Abstract.lean)
- `TSSN.unramifiedAt_of_subring` (PROVED, VERIFIED compile, axioms [propext, Classical.choice,
  Quot.sound]): `L ⊂ ℚ̄` finite over ℚ, `A ⊆ L` Noetherian subring with Frac A = L, integers prime
  to p units in A, every y ∈ A has n·y integral over ℤ for some n prime to p, maximal ideals of A
  contain p, and for primes q ∋ p, `maximalIdeal A_q = (p)` ⇒ `UnramifiedAt L p`.
  Route: A_q DVR (`IsDiscreteValuationRing.TFAE` out 1 5) ⇒ A normal
  (`IsIntegrallyClosed.of_localization_maximal`) ⇒ 𝓞_L ⊆ A ⇒ A = (𝓞_L)[1/n : p∤n]
  (IsLocalization) ⇒ (𝓞_L)_Q ≅ A_{QA} (`isLocalization_isLocalization_atPrime_isLocalization`)
  ⇒ `(Q.under ℤ).map = (p)` maximal ⇒ `ramificationIdx = 1` (length-one unfolding as in Mathlib's
  `Ideal.ramificationIdx_eq_one`).
