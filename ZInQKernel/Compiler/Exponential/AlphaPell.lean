import ZInQKernel.Compiler.Exponential.AlphaGrowth
import ZInQ.AlphaIndexCompanion

/-!
# Natural solutions of the alpha Pell equation

Blueprint: `compiler/natural/exponential/alpha-pell.md`.

1. For `b > 2`, every natural solution of `x² + y² = 1 + bxy` is an adjacent pair
   `{α_b(n), α_b(n+1)}` (in either order).
2. For every `b`, an ordered solution `r < s` of `s² + r² = 1 + bsr` is
   `(α_b(m-1), α_b(m))` with `m > 0` (upstream `orderedPair_positive_index`).
3. For `b ≥ 2`, adjacent pairs are natural, ordered, and solve the equation.

The descent is upstream's `alphaZ_descent`.
-/

namespace ZInQ.AlphaPower

/-- Unordered classification: for `b > 2`, a natural solution of `x² + y² = 1 + bxy` is
`{x, y} = {α_b(n), α_b(n+1)}` for some `n`. -/
theorem alphaZ_pell_unordered {b x y : ℕ} (hb : 2 < b) (h : x ^ 2 + y ^ 2 = 1 + b * x * y) :
    ∃ n : ℕ, ((x : ℤ) = alphaZ b n ∧ (y : ℤ) = alphaZ b (n + 1)) ∨
      ((x : ℤ) = alphaZ b (n + 1) ∧ (y : ℤ) = alphaZ b n) := by
  have hne : x ≠ y := by
    rintro rfl
    have hmul : 2 * (x * x) ≤ b * (x * x) := Nat.mul_le_mul_right (x * x) hb.le
    nlinarith only [h, hmul]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨n, hx, hy⟩ := alphaZ_descent b x y hlt (by nlinarith only [h])
    exact ⟨n, Or.inl ⟨hx, hy⟩⟩
  · obtain ⟨n, hy, hx⟩ := alphaZ_descent b y x hgt (by nlinarith only [h])
    exact ⟨n, Or.inr ⟨hx, hy⟩⟩

/-- In particular each coordinate of an unordered solution is an alpha value. -/
theorem alphaZ_pell_index {b x y : ℕ} (hb : 2 < b) (h : x ^ 2 + y ^ 2 = 1 + b * x * y) :
    ∃ n : ℕ, (x : ℤ) = alphaZ b n := by
  obtain ⟨n, ⟨hx, -⟩ | ⟨hx, -⟩⟩ := alphaZ_pell_unordered hb h
  exacts [⟨n, hx⟩, ⟨n + 1, hx⟩]

/-- Ordered classification, for every natural `b`. -/
theorem alphaZ_pell_ordered (b : ℕ) {r s : ℕ} (hrs : r < s)
    (h : s ^ 2 + r ^ 2 = 1 + b * s * r) :
    ∃ m : ℕ, 0 < m ∧ (r : ℤ) = alphaZ b (m - 1) ∧ (s : ℤ) = alphaZ b m :=
  orderedPair_positive_index b r s hrs h

/-- Converse: for `b ≥ 2` the adjacent pair `(α_b(n), α_b(n+1))` is a pair of naturals with
`α_b(n) < α_b(n+1)` solving the equation. -/
theorem alphaZ_pell_converse (b : ℕ) (hb : 2 ≤ b) (n : ℕ) :
    ∃ x y : ℕ, (x : ℤ) = alphaZ b n ∧ (y : ℤ) = alphaZ b (n + 1) ∧ x < y ∧
      x ^ 2 + y ^ 2 = 1 + b * x * y := by
  have h0 := alphaZ_nonneg b hb n
  have h1 := alphaZ_nonneg b hb (n + 1)
  refine ⟨(alphaZ b n).toNat, (alphaZ b (n + 1)).toNat, Int.toNat_of_nonneg h0,
    Int.toNat_of_nonneg h1, ?_, ?_⟩
  · have := alphaZ_succ_strict b n hb
    omega
  · have hc := alphaZ_cassini b n
    have : (((alphaZ b n).toNat ^ 2 + (alphaZ b (n + 1)).toNat ^ 2 : ℕ) : ℤ) =
        ((1 + b * (alphaZ b n).toNat * (alphaZ b (n + 1)).toNat : ℕ) : ℤ) := by
      push_cast
      rw [Int.toNat_of_nonneg h0, Int.toNat_of_nonneg h1]
      linear_combination hc
    exact_mod_cast this

end ZInQ.AlphaPower
