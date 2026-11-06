# Implementation note: Odd alpha values are unbounded

- Lean name: reuse `ZInQ.AlphaPower.alphaZ_large_odd_pair` (AlphaLargeOddPair).
- Draft (exists): `theorem alphaZ_large_odd_pair (B a : ℕ) (hB : 3 < B) : ∃ k, 0 < k ∧
  Odd (alphaZ B k) ∧ 2 * (a : ℤ) < alphaZ B k ∧ alphaZ B k < alphaZ B (k + 1) ∧ ...`.
- FINITE COMPUTATION: no. Difficulty: none (exists).
