# Implementation note: Matrix powers and the quadratic identity

- Lean names: `ZInQ.AlphaPower.alphaMat_pow`, reuse `alphaZ_cassini`, `alphaZ_consecutive_coprime`,
  `alphaZ_mod_two_eq_one_or_succ`, `alphaZ_add_succ`.
- Draft:
  ```lean
  theorem alphaMat_pow (b n : ℕ) (hn : 1 ≤ n) :
      (!![(b : ℤ), -1; 1, 0]) ^ n =
        !![alphaZ b (n+1), -alphaZ b n; alphaZ b n, -alphaZ b (n-1)]
  ```
- Mathlib: `Matrix.det_fin_two`, `Matrix.det_pow`, `pow_succ`, `Matrix.mul_fin_two`.
- Upstream reuse: `AlphaCore.alphaZ_cassini` (item 2), `AlphaSquareDivisibilityDraft.alphaZ_consecutive_coprime`
  (item 3, `IsCoprime`), `AlphaParity.alphaZ_mod_two_eq_one_or_succ` (parity),
  `AlphaAddition.alphaZ_add_succ` (item 4). Only item 1 is new, and nothing else in the chapter
  needs it (the upstream proofs avoid matrices); it may be omitted from Lean.
- FINITE COMPUTATION: no. Difficulty: easy.
