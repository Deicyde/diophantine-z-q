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

## Step 2: SNSpecialize PROVED (scratch/ts-sn/TSSN.lean), compiled 2026-11-13 ~10:00 PST
- `TSSN.lean` = verbatim `PropTSGlue.lean` (`check_prefix.py`: PREFIX IDENTICAL) + appendix.
- `lake env lean scratch/ts-sn/TSSN.lean`: 0 errors, 0 sorry, 71 linter warnings; all 69
  `#print axioms` lines `[propext, Classical.choice, Quot.sound]` (VERIFIED, compile_out.txt).
- New theorems: `homog_data` (g ∈ m ↔ p ∣ d^k g(s₀)), `snSpecialize_aux`, `snSpecialize :
  SNSpecialize`, `verticalResidueSeparable : VerticalResidueSeparable`, `specNonMeeting :
  SpecNonMeeting`, `propTSAll_final'` (12 open glue Props: 7 Kummer + 5 Hecke; plus T2, R1R2fp,
  MobiusGlue).
- Route of `snSpecialize_aux`: ρ : C → B/𝔓 → L (L = ℚ(φ(B/𝔓))), ρ(g) = g(s₀) on ℤ[X];
  ψ : S = C_m → L by `IsLocalization.lift` (g ∉ m ⇒ g(s₀) ≠ 0 by `homog_data`); A := ψ(S).
  L = range φ (Subalgebra from `adjoin_toSubalgebra_of_isAlgebraic`), finite over ℚ via the
  ℚ[X]-generators of B (φ(f·b) = f(s₀)φ(b)). Hypotheses of `unramifiedAt_of_subring`:
  Noetherian (finite over R); units (C n ∉ m); maximal ideals ∋ p (integral over local R);
  `maximalIdeal A_q = (p)` from `Algebra.FormallyUnramified.map_maximalIdeal` for R → A_q
  (étale R → S, `of_surjective`, localization) and m ↦ pA (`homog_data`); Frac A = L (integer
  multiples of B land in C: `exists_multiple_integral_of_isLocalization`); n·y integral over ℤ
  (ρ(c) integral over ℤ[1/d] through `Localization.Away d`).
- Pitfalls: `Module ℚ (B ⧸ 𝔓)` instance search times out (avoid ℚ-structures on the quotient; work
  with the ℚ-subalgebra range φ ⊆ ℚ̄); `map_add φ` typeclass timeout (use `φ.map_add`);
  `ψ.range`/`rangeRestrict` instance-path mismatch for subalgebra domains (use `@RingHom.range`
  and a hand-built `ψA`); `set` on big terms is slow (use `let`); `IsScalarTower ℤ Zd L` needs the
  `@... Algebra.toSMul` form.
