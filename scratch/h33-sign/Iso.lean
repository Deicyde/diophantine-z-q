import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # h33-sign: algebraic checks of the normalizations in `TYZThm33` (Mathlib only)

* TYZ's `A : 2y² = x³ + x` (Period7.tex L1173) and the kernel's `curveA : y² = x³ + 4x` are
  isomorphic by `(x, y) ↦ (2x, 4y)`, and the map commutes with `[i] : (x, y) ↦ (−x, i·y)`.
* TYZ's `E_n : n y² = x³ − x` (L312) and the kernel's `curveC n : y² = x³ − n² x` are isomorphic by
  `(x, y) ↦ (n x, n² y)`.
* The fixed points of TYZ's embeddings `K_n → M₂(ℚ)` (L1203–1205) are the roots of the kernel's
  Heegner forms `tyzForm n = [16(n+1), −8, 1]` (`n ≡ 5`) and `tyzForm7 n = [(n+δ²)/4, δ, 1]` (`n ≡ 7`),
  with the discriminants `−64n` and `−n`.
-/

theorem tyzA_to_kernelA {K : Type*} [Field K] (x y : K) (h : 2 * y ^ 2 = x ^ 3 + x) :
    (4 * y) ^ 2 = (2 * x) ^ 3 + 4 * (2 * x) := by
  linear_combination 8 * h

theorem kernelA_to_tyzA {K : Type*} [Field K] [CharZero K] (X Y : K) (h : Y ^ 2 = X ^ 3 + 4 * X) :
    2 * (Y / 4) ^ 2 = (X / 2) ^ 3 + X / 2 := by
  linear_combination h / 8

/-- The isomorphism commutes with `[i]`: image of `(−x, i y)` is `(−(2x), i (4y))`. -/
theorem iso_comm_i {K : Type*} [Field K] (i x y : K) :
    (2 * (-x), 4 * (i * y)) = (-(2 * x), i * (4 * y)) := by
  ext <;> ring

/-- `[i]` preserves the kernel's curve iff `i² = −1` (given a point with `y ≠ 0`). -/
theorem i_preserves_kernelA {K : Type*} [Field K] (i X Y : K) (hi : i ^ 2 = -1)
    (h : Y ^ 2 = X ^ 3 + 4 * X) : (i * Y) ^ 2 = (-X) ^ 3 + 4 * (-X) := by
  linear_combination Y ^ 2 * hi - h

theorem tyzE_to_curveC {K : Type*} [Field K] (n x y : K) (h : n * y ^ 2 = x ^ 3 - x) :
    (n ^ 2 * y) ^ 2 = (n * x) ^ 3 - n ^ 2 * (n * x) := by
  linear_combination n ^ 3 * h

/-- `n ≡ 5`: `h = (−h + 1/4)/(−4(n+1)h + 1)` iff `16(n+1)h² − 8h + 1 = 0` (denominator nonzero). -/
theorem fixed5 {K : Type*} [Field K] [CharZero K] (n h : K) (hd : -4 * (n + 1) * h + 1 ≠ 0) :
    (-h + 1 / 4) / (-4 * (n + 1) * h + 1) = h ↔ 16 * (n + 1) * h ^ 2 - 8 * h + 1 = 0 := by
  rw [div_eq_iff hd]
  constructor
  · intro e; linear_combination 4 * e
  · intro e; linear_combination e / 4

/-- `n ≡ 7`: `h = (δh + 2)/(−(n+δ²)/2·h − δ)` iff `(n+δ²)/4·h² + δh + 1 = 0`. -/
theorem fixed7 {K : Type*} [Field K] [CharZero K] (n δ h : K) (hd : -(n + δ ^ 2) / 2 * h - δ ≠ 0) :
    (δ * h + 2) / (-(n + δ ^ 2) / 2 * h - δ) = h ↔ (n + δ ^ 2) / 4 * h ^ 2 + δ * h + 1 = 0 := by
  rw [div_eq_iff hd]
  constructor
  · intro e; linear_combination e / 2
  · intro e; linear_combination 2 * e

theorem disc5 (n : ℤ) : (-8) ^ 2 - 4 * (16 * (n + 1)) * 1 = -64 * n := by ring

theorem disc7 (n δ : ℤ) (h : 4 ∣ n + δ ^ 2) : δ ^ 2 - 4 * ((n + δ ^ 2) / 4) * 1 = -n := by
  obtain ⟨k, hk⟩ := h
  rw [hk, Int.mul_ediv_cancel_left _ (by norm_num)]
  linear_combination hk
