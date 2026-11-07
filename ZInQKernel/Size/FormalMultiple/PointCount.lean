import ZInQKernel.Model.Field.ShortWeierstrass

/-!
# The trivial point count

Blueprint: `size/formal-multiple/trivial-point-count.md`.

Over a finite field `k`, the curve `y² = x³ + a x` has at most `2 |k|` affine points (for each
`x` there are at most two `y` with `y² = c`), so its group of nonsingular points (Mathlib's
`Point`, which consists of `O` and the nonsingular affine points) has at most `2 |k| + 1`
elements, and every point has order at most `2 |k| + 1`. This replaces Hasse's bound. For an
odd prime `p`, `2 p² + 1 ≤ p⁶` and `(2 p + 1)² ≤ p⁶`.

The article assumes `k` of odd characteristic; the count holds in every characteristic.
-/

namespace ZInQ.Size

open WeierstrassCurve WeierstrassCurve.Affine

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k]

/-- The affine solutions of `y² = x³ + a x` in `k²`. -/
def affineSolutions (a : k) : Finset (k × k) :=
  Finset.univ.filter fun xy => xy.2 ^ 2 = xy.1 ^ 3 + a * xy.1

/-- **The affine count**: `#{(x, y) ∈ k² : y² = x³ + a x} ≤ 2 |k|`. -/
theorem card_affineSolutions_le (a : k) : (affineSolutions a).card ≤ 2 * Fintype.card k := by
  refine (Finset.card_le_mul_card_image (f := Prod.fst) _ 2 ?_).trans
    (Nat.mul_le_mul_left 2 (Finset.card_le_univ _))
  intro x _
  by_cases hne : ((affineSolutions a).filter fun xy => xy.1 = x).Nonempty
  · obtain ⟨⟨x₀, y₀⟩, h₀⟩ := hne
    simp only [affineSolutions, Finset.mem_filter, Finset.mem_univ, true_and] at h₀
    obtain ⟨e₀, rfl⟩ := h₀
    refine le_trans (Finset.card_le_card ?_) (Finset.card_le_two (a := (x₀, y₀)) (b := (x₀, -y₀)))
    rintro ⟨x', y'⟩ h
    simp only [affineSolutions, Finset.mem_filter, Finset.mem_univ, true_and] at h
    obtain ⟨e, rfl⟩ := h
    have : y' ^ 2 = y₀ ^ 2 := by rw [e, e₀]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp this with h | h <;> simp [h]
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]; simp

/-- Points of `y² = x³ + a x` as elements of `Option (k × k)`. -/
def pointToOption {a : k} : (shortCurve a).toAffine.Point → Option (affineSolutions a)
  | .zero => none
  | .some x y h => some ⟨(x, y), by
      simp only [affineSolutions, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (shortCurve_equation_iff a x y).mp h.1⟩

theorem pointToOption_injective (a : k) :
    Function.Injective (pointToOption (a := a)) := by
  rintro (_ | ⟨x, y, h⟩) (_ | ⟨x', y', h'⟩) e
  · rfl
  · simp [pointToOption] at e
  · simp [pointToOption] at e
  · simp only [pointToOption, Option.some.injEq, Subtype.mk.injEq, Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rfl

instance finite_point (a : k) : Finite (shortCurve a).toAffine.Point :=
  Finite.of_injective _ (pointToOption_injective a)

/-- **The trivial point count**: the group of nonsingular points of `y² = x³ + a x` over a
finite field `k` has at most `2 |k| + 1` elements. -/
theorem card_points_le (a : k) :
    Nat.card (shortCurve a).toAffine.Point ≤ 2 * Fintype.card k + 1 := by
  refine (Nat.card_le_card_of_injective _ (pointToOption_injective a)).trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_coe]
  exact Nat.add_le_add_right (card_affineSolutions_le a) 1

/-- Every point of `y² = x³ + a x` over a finite field `k` has order at most `2 |k| + 1`. -/
theorem addOrderOf_le_two_card_add_one (a : k) (P : (shortCurve a).toAffine.Point) :
    addOrderOf P ≤ 2 * Fintype.card k + 1 :=
  (addOrderOf_le_card (x := P)).trans (card_points_le a)

omit [Fintype k] in
/-- The same bound with `Nat.card`, for a finite field without a chosen `Fintype` structure. -/
theorem addOrderOf_le_two_natCard_add_one [Finite k] (a : k)
    (P : (shortCurve a).toAffine.Point) : addOrderOf P ≤ 2 * Nat.card k + 1 := by
  have := Fintype.ofFinite k
  rw [Nat.card_eq_fintype_card]
  exact addOrderOf_le_two_card_add_one a P

/-- `2 p² + 1 ≤ p⁶` and `(2 p + 1)² ≤ p⁶` for `p ≥ 3`. -/
theorem odd_prime_count_bounds {p : ℕ} (hp : 3 ≤ p) :
    2 * p ^ 2 + 1 ≤ p ^ 6 ∧ (2 * p + 1) ^ 2 ≤ p ^ 6 := by
  have h1 : 2 * p + 1 ≤ p ^ 3 := by
    have : 3 * p ≤ p * p := Nat.mul_le_mul_right p hp
    have : p * p ≤ p ^ 3 := by nlinarith
    nlinarith
  constructor
  · nlinarith [Nat.pow_le_pow_left hp 2, Nat.pow_le_pow_left hp 4]
  · calc (2 * p + 1) ^ 2 ≤ (p ^ 3) ^ 2 := Nat.pow_le_pow_left h1 2
      _ = p ^ 6 := by ring

end ZInQ.Size
