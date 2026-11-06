# Implementation note: Period and reflection modulo the companion

- Lean names: reuse `exists_folded_index` (AlphaIndexCompanion, item 1),
  `companion_dvd_alphaZ_add_period`, `companion_dvd_alphaZ_reflection` (AlphaPeriodReflection,
  item 2), `folded_alpha_signed_residue` (AlphaFoldedResidue, the folded form),
  `two_mul_alphaZ_lt_companion` (AlphaCompanionBound, item 3), `companion_of_additive_witness`
  and `exists_large_additive_companion` (AlphaIndexCompanion, `v = b s - 2 r` and `v > 2 s`).
- Draft (exists): `theorem two_mul_alphaZ_lt_companion (B j m : ℕ) (hB : 3 < B) (hm : 0 < m)
  (hjm : j ≤ m) : 2 * alphaZ B j < alphaZ B (m + 1) - alphaZ B (m - 1)`.
- Mathlib: `Int.dvd_sub`, `pow_mul`, `neg_one_pow`.
- FINITE COMPUTATION: no. Difficulty: none (exists).
