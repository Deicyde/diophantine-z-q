import Mathlib
import ZInQKernel.Model.Field.ShortWeierstrass

/-!
# tyz-318: the supersingular exponent of `y² = x³ + 4x`, elementary (weak form)

For `p ≡ 3 (mod 4)` and a field `k ⊆ F_{p²}` of characteristic `p` containing `√−1`, every point of
`y² = x³ + 4x` over `k` is killed by `2(p + 1)`.

Proof: `#E(F_p) = p + 1` (pairing `x ↔ −x`, `−1` a non-square); the `p`-power Frobenius `π` and
`[i] : (x, y) ↦ (−x, iy)` satisfy `π² = 1`, `π[i] = −[i]π`; `P + πP` and `[i](P − πP)` are fixed by
`π`, hence `F_p`-points, hence killed by `p + 1`.
-/

noncomputable section

namespace ZInQ.Contrib.TYZGenus.T318SS

open WeierstrassCurve WeierstrassCurve.Affine

/-! ## §1. Counting `E(F_p)` -/

section Count

variable {F : Type*} [Field F] [DecidableEq F]

/-- Points of an affine Weierstrass curve: `O` or an affine nonsingular solution. -/
def ptEquiv (W : WeierstrassCurve.Affine F) :
    W.Point ≃ Option {xy : F × F // W.Nonsingular xy.1 xy.2} where
  toFun
    | .zero => none
    | .some x y h => some ⟨(x, y), h⟩
  invFun
    | none => .zero
    | some xy => .some xy.1.1 xy.1.2 xy.2
  left_inv P := by cases P <;> rfl
  right_inv o := by rcases o with _ | ⟨⟨x, y⟩, h⟩ <;> rfl

variable (p : ℕ) [hp : Fact p.Prime]

/-- `y² = x³ + 4x` over `F_p`. -/
abbrev W1 : WeierstrassCurve.Affine (ZMod p) := (ZInQ.shortCurve (4 : ZMod p)).baseChange (ZMod p)

theorem W1_nonsingular_iff (hp2 : p ≠ 2) (x y : ZMod p) :
    (W1 p).Nonsingular x y ↔ y ^ 2 = x ^ 3 + 4 * x := by
  have hΔ : (W1 p).Δ ≠ 0 := by
    have h1 : (W1 p).Δ = -4096 := by
      rw [W1, WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ, ZInQ.shortCurve_Δ]
      simp; norm_num
    rw [h1, neg_ne_zero]
    have h2 : (4096 : ZMod p) = (2 : ZMod p) ^ 12 := by norm_num
    rw [h2]
    apply pow_ne_zero
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  rw [← equation_iff_nonsingular_of_Δ_ne_zero hΔ, equation_iff]
  simp [W1, WeierstrassCurve.baseChange, WeierstrassCurve.map]

theorem ringChar_ne_two (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; exact hp2

theorem sum_quadraticChar_f (hp4 : p % 4 = 3) :
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + 4 * x) = 0 := by
  have hp2 : p ≠ 2 := by omega
  have hneg : quadraticChar (ZMod p) (-1) = -1 := by
    rw [quadraticChar_neg_one (ringChar_ne_two p hp2), ZMod.card, ZMod.χ₄_nat_three_mod_four hp4]
  have hS : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + 4 * x) =
      ∑ x : ZMod p, quadraticChar (ZMod p) ((-x) ^ 3 + 4 * (-x)) :=
    (Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ (fun x => rfl)).symm
  have hS' : ∑ x : ZMod p, quadraticChar (ZMod p) ((-x) ^ 3 + 4 * (-x)) =
      -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + 4 * x) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro x _
    rw [show (-x) ^ 3 + 4 * (-x) = (-1) * (x ^ 3 + 4 * x) by ring, map_mul, hneg, neg_one_mul]
  rw [hS'] at hS
  linarith

theorem card_W1 (hp4 : p % 4 = 3) : Nat.card (W1 p).Point = p + 1 := by
  classical
  have hp2 : p ≠ 2 := by omega
  rw [Nat.card_congr (ptEquiv (W1 p)), Finite.card_option]
  congr 1
  have e1 : Nat.card {xy : ZMod p × ZMod p // (W1 p).Nonsingular xy.1 xy.2} =
      Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 + 4 * xy.1} :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun xy => W1_nonsingular_iff p hp2 xy.1 xy.2))
  rw [e1, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter,
    Fintype.sum_prod_type]
  have h1 : ∀ x : ZMod p, (∑ y : ZMod p, if y ^ 2 = x ^ 3 + 4 * x then 1 else 0 : ℕ) =
      (Set.toFinset {y : ZMod p | y ^ 2 = x ^ 3 + 4 * x}).card := by
    intro x
    rw [← Finset.card_filter]
    congr 1
    ext y
    simp
  simp_rw [h1]
  have h2 : ((∑ x : ZMod p, (Set.toFinset {y : ZMod p | y ^ 2 = x ^ 3 + 4 * x}).card : ℕ) : ℤ) =
      (p : ℤ) := by
    push_cast
    simp_rw [quadraticChar_card_sqrts (ringChar_ne_two p hp2)]
    rw [Finset.sum_add_distrib, sum_quadraticChar_f p hp4]
    simp
  exact_mod_cast h2

end Count

end ZInQ.Contrib.TYZGenus.T318SS
