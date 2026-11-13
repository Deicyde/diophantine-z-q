# hecke-all results log

## LocalCd.lean (VERIFIED: compiles, `lake build ZInQKernel.Contrib.HeckeAll.LocalCd`, 22:15; axioms propext, Classical.choice, Quot.sound)
- `isMinimal_baseChange_of_c₄`: integral W over a DVR is minimal if `W.c₄ ≠ r⁴ c₄(W')` for all r ∈ 𝔪, W' integral.
- `c₄_two_adic`: over ℤ₂ (natGenerator v = 2), every integral model has `16 ∣ c₄` (a₁ ∈ 𝔪) or `c₄ ∉ 𝔪`.
- `isMinimal_cdLocal_two`: y² = x³ − (2e)²x is minimal at 2 for odd e (v₂(c₄) = 6).
- `isMinimal_cdLocal'`: y² = x³ − d²x minimal at every place for squarefree d (any parity).
- `hasAdditiveReduction_cdLocal'`, `localPolynomial_cdLocal_eq'`, `LFunction_cd_apply_prime_pow'`,
  `LFunction_cd_apply_prime'`, `LFunction_cd_apply'`, `LFunction_cd_apply_prime_eq_sub_card'`,
  `LFunction_cd_apply_prime_of_dvd'`, `LSeries_cd_eq'`: LFunctionCd.lean's results for every squarefree d.

## Iso.lean (VERIFIED: compiles, `lake env lean`, 22:20, no errors)
- `not_hasMultiplicativeReduction_smul`: v(c₄)³ ≤ v(Δ) (integral j) ⇒ no model C • W has multiplicative reduction.
- `localPolynomial_eq_ite`, `localPolynomial_smul`: Mathlib's `localPolynomial` is invariant under any change of
  variables when j is integral (both minimal models differ by v(u) = 1; good/additive classes and #W̃(κ) agree).
- `hj_cdLocal` (c₄³ = 1728Δ for C_d), `scaleChange`, `scaleChange_smul`, `LFunction_cd_sq_mul`,
  `LSeries_cd_sq_mul`: L(C_{m²d}, s) = L(C_d, s) for d, m ≠ 0.
