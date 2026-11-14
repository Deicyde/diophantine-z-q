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

/-! ## §2. `[i]` on a curve `y² = x³ + a₄x` over a field with `ι² = −1` -/

section IMap

variable {k : Type*} [Field k] [DecidableEq k] (C : WeierstrassCurve k)
  (ha₁ : C.a₁ = 0) (ha₂ : C.a₂ = 0) (ha₃ : C.a₃ = 0) (ha₆ : C.a₆ = 0)
  {ι : k} (hι : ι ^ 2 = -1)

include ha₁ ha₂ ha₃ ha₆ hι

theorem ι_ne_zero : ι ≠ 0 := by
  intro h; rw [h] at hι; have : (0 : k) = -1 := by simpa using hι
  exact one_ne_zero (neg_eq_zero.mp this.symm)

theorem nonsingular_iK {x y : k} (h : C.toAffine.Nonsingular x y) :
    C.toAffine.Nonsingular (-x) (ι * y) := by
  have hι0 := ι_ne_zero C ha₁ ha₂ ha₃ ha₆ hι
  rw [WeierstrassCurve.Affine.nonsingular_iff', WeierstrassCurve.Affine.equation_iff'] at h ⊢
  simp only [ha₁, ha₂, ha₃, ha₆] at h ⊢
  obtain ⟨he, hn⟩ := h
  refine ⟨by linear_combination y ^ 2 * hι - he, ?_⟩
  rcases hn with h | h
  · left
    intro h'
    apply h
    linear_combination h'
  · right
    intro h'
    apply h
    have : ι * (2 * y) = 0 := by linear_combination h'
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd h0 hι0
    · linear_combination h0

/-- `[i]` : `O ↦ O`, `(x, y) ↦ (−x, ιy)`. -/
def iK : C.toAffine.Point → C.toAffine.Point
  | .zero => .zero
  | .some x y h => .some (-x) (ι * y) (nonsingular_iK C ha₁ ha₂ ha₃ ha₆ hι h)

theorem iK_some {x y : k} (h : C.toAffine.Nonsingular x y) :
    iK C ha₁ ha₂ ha₃ ha₆ hι (.some x y h) = .some (-x) (ι * y) (nonsingular_iK C ha₁ ha₂ ha₃ ha₆ hι h) :=
  rfl

theorem div_iota_mul (A B : k) : A / (ι * B) = -ι * (A / B) := by
  have hι0 := ι_ne_zero C ha₁ ha₂ ha₃ ha₆ hι
  have hinv : ι⁻¹ = -ι := by
    apply inv_eq_of_mul_eq_one_right
    linear_combination -hι
  rw [mul_comm ι B, ← div_div, div_eq_mul_inv _ ι, hinv]
  ring

theorem slope_iK (x₁ x₂ y₁ y₂ : k) :
    C.toAffine.slope (-x₁) (-x₂) (ι * y₁) (ι * y₂) = -ι * C.toAffine.slope x₁ x₂ y₁ y₂ := by
  have hι0 := ι_ne_zero C ha₁ ha₂ ha₃ ha₆ hι
  by_cases hx : x₁ = x₂
  · have hx' : -x₁ = -x₂ := by rw [hx]
    by_cases hy : y₁ = C.toAffine.negY x₂ y₂
    · have hy' : ι * y₁ = C.toAffine.negY (-x₂) (ι * y₂) := by
        simp only [negY, ha₁, ha₃] at hy ⊢
        rw [hy]; ring
      rw [slope_of_Y_eq hx hy, slope_of_Y_eq hx' hy', mul_zero]
    · have hy' : ι * y₁ ≠ C.toAffine.negY (-x₂) (ι * y₂) := by
        simp only [negY, ha₁, ha₃] at hy ⊢
        intro h
        apply hy
        have : ι * (y₁ - (-y₂ - 0 * x₂ - 0)) = 0 := by linear_combination h
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hι0
        · linear_combination h0
      rw [slope_of_Y_ne hx hy, slope_of_Y_ne hx' hy']
      simp only [negY, ha₁, ha₂, ha₃]
      rw [show ι * y₁ - (-(ι * y₁) - 0 * -x₁ - 0) = ι * (y₁ - (-y₁ - 0 * x₁ - 0)) by ring,
        div_iota_mul C ha₁ ha₂ ha₃ ha₆ hι]
      congr 2
      ring
  · have hx' : -x₁ ≠ -x₂ := fun h => hx (neg_injective h)
    rw [slope_of_X_ne hx, slope_of_X_ne hx']
    rw [show -x₁ - -x₂ = -(x₁ - x₂) by ring, div_neg,
      show ι * y₁ - ι * y₂ = ι * (y₁ - y₂) by ring]
    ring

theorem iK_add (P Q : C.toAffine.Point) :
    iK C ha₁ ha₂ ha₃ ha₆ hι (P + Q) = iK C ha₁ ha₂ ha₃ ha₆ hι P + iK C ha₁ ha₂ ha₃ ha₆ hι Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · rfl
  · rfl
  · have hι0 := ι_ne_zero C ha₁ ha₂ ha₃ ha₆ hι
    by_cases hxy : x₁ = x₂ ∧ y₁ = C.toAffine.negY x₂ y₂
    · have hxy' : -x₁ = -x₂ ∧ ι * y₁ = C.toAffine.negY (-x₂) (ι * y₂) := by
        refine ⟨by rw [hxy.1], ?_⟩
        have := hxy.2
        simp only [negY, ha₁, ha₃] at this ⊢
        rw [this]; ring
      rw [Point.add_of_Y_eq hxy.1 hxy.2, iK_some, iK_some, Point.add_of_Y_eq hxy'.1 hxy'.2]
      rfl
    · have hxy' : ¬(-x₁ = -x₂ ∧ ι * y₁ = C.toAffine.negY (-x₂) (ι * y₂)) := by
        rintro ⟨h1, h2⟩
        apply hxy
        refine ⟨neg_injective h1, ?_⟩
        simp only [negY, ha₁, ha₃] at h2 ⊢
        have : ι * (y₁ - (-y₂ - 0 * x₂ - 0)) = 0 := by linear_combination h2
        rcases mul_eq_zero.mp this with h0 | h0
        · exact absurd h0 hι0
        · linear_combination h0
      rw [Point.add_some hxy, iK_some, iK_some, iK_some, Point.add_some hxy', Point.some.injEq]
      have hs := slope_iK C ha₁ ha₂ ha₃ ha₆ hι x₁ x₂ y₁ y₂
      constructor
      · simp only [addX, ha₁, ha₂]
        rw [hs]
        linear_combination (-(C.toAffine.slope x₁ x₂ y₁ y₂) ^ 2) * hι
      · simp only [addY, negAddY, addX, negY, ha₁, ha₂, ha₃]
        rw [hs]
        linear_combination (-ι * C.toAffine.slope x₁ x₂ y₁ y₂ ^ 3) * hι

theorem iK_iK (P : C.toAffine.Point) :
    iK C ha₁ ha₂ ha₃ ha₆ hι (iK C ha₁ ha₂ ha₃ ha₆ hι P) = -P := by
  rcases P with _ | ⟨x, y, h⟩
  · rfl
  · rw [iK_some, iK_some, Point.neg_some, Point.some.injEq]
    refine ⟨neg_neg x, ?_⟩
    simp only [negY, ha₁, ha₃]
    linear_combination y * hι

/-- `[i]` as an additive map. -/
def iKHom : C.toAffine.Point →+ C.toAffine.Point :=
  AddMonoidHom.mk' (iK C ha₁ ha₂ ha₃ ha₆ hι) (iK_add C ha₁ ha₂ ha₃ ha₆ hι)

end IMap

end ZInQ.Contrib.TYZGenus.T318SS
