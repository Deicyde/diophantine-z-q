# Implementation note: Character sums are bounded by the modulus

- Owner: pp-lseries (plan step 1), `ZInQKernel/Progressions/LSeries/`. Namespace `ZInQ.Progressions`; modules import Mathlib (and earlier `Progressions` modules) only.
- Lean name: `ZInQ.Progressions.norm_sum_char_le` (pushed on `wip/pp-lseries`, `LSeries/CharSum.lean`, with the interval form `norm_sum_Ioc_char_le`).
- Draft:
  ```lean
  variable {q : ℕ} [NeZero q]
  theorem norm_sum_char_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (x : ℝ) :
      ‖∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ n‖ ≤ q
  theorem norm_sum_Ioc_char_le {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (a b : ℕ) :
      ‖∑ n ∈ Finset.Ioc a b, χ n‖ ≤ q
  ```
- Mathlib: `MulChar.sum_eq_zero_of_ne_one`, `Finset.sum_Ico_eq_sum_range`, `Finset.sum_nbij'`.
- Difficulty: easy (done upstream of this note).
