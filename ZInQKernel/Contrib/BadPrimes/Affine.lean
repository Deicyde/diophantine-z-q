import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Affine counts for singular congruent-number equations

The cusp `y² = x³` is parametrized bijectively by `t ↦ (t², t³)` over
any field. The inverse is `y / x`, with total field division returning
zero at the origin. Thus the cusp has exactly `#F` affine points over
a finite field, in every characteristic.

Over `ZMod 2`, squaring is the identity, so each equation `y² = f x`
is the graph of `f`. This counts the congruent-number affine equation
for every natural number `d`, with no oddness or squarefreeness assumption.
-/

namespace ZInQ.Contrib.BadPrimes

/-- The field-valued affine cusp is bijectively parametrized by `(t², t³)`.
Its inverse is `y / x`, which equals zero at the origin. -/
def affineCuspEquiv (F : Type*) [Field F] :
    F ≃ {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3} where
  toFun t := ⟨(t ^ 2, t ^ 3), by dsimp; ring⟩
  invFun P := P.1.2 / P.1.1
  left_inv t := by
    by_cases ht : t = 0
    · simp [ht]
    · dsimp
      field_simp
  right_inv P := by
    obtain ⟨⟨x, y⟩, h⟩ := P
    dsimp at h
    apply Subtype.ext
    change ((y / x) ^ 2, (y / x) ^ 3) = (x, y)
    apply Prod.ext
    · change (y / x) ^ 2 = x
      by_cases hx : x = 0
      · simp [hx]
      · rw [div_pow, h]
        field_simp
    · change (y / x) ^ 3 = y
      by_cases hx : x = 0
      · have hy : y = 0 := by simpa [hx] using h
        simp [hx, hy]
      · have hs : (y / x) ^ 2 = x := by
          rw [div_pow, h]
          field_simp
        rw [pow_succ, hs]
        field_simp

/-- The affine cusp has exactly one point per field element over any finite field. -/
theorem natCard_affine_cusp (F : Type*) [Field F] [Fintype F] :
    Nat.card {xy : F × F // xy.2 ^ 2 = xy.1 ^ 3} = Fintype.card F := by
  rw [← Nat.card_eq_fintype_card]
  exact Nat.card_congr (affineCuspEquiv F).symm

/-- Since squaring is the identity over `ZMod 2`, the equation `y² = f x`
is bijective with the graph parameter `x`, for any function `f`. -/
def affineSquareTwoEquiv (f : ZMod 2 → ZMod 2) :
    ZMod 2 ≃ {xy : ZMod 2 × ZMod 2 // xy.2 ^ 2 = f xy.1} where
  toFun x := ⟨(x, f x), ZMod.pow_card (f x)⟩
  invFun P := P.1.1
  left_inv _ := rfl
  right_inv P := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact P.2.symm.trans (ZMod.pow_card P.1.2)

/-- At `p = 2`, the affine congruent-number equation has two solutions for every `d`. -/
theorem natCard_affine_cd_two (d : ℕ) :
    Nat.card {xy : ZMod 2 × ZMod 2 //
      xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod 2) ^ 2 * xy.1} = 2 := by
  rw [Nat.card_congr
    (affineSquareTwoEquiv (fun x => x ^ 3 - (d : ZMod 2) ^ 2 * x)).symm,
    Nat.card_zmod]

end ZInQ.Contrib.BadPrimes
