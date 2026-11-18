import ZInQKernel.Contrib.CloudB3RC53.Calibration.EdixhovenModel

/-!
# Calibration: a concrete non-trivial instance of the Edixhoven print's hypotheses (PROVED)

For `ℓ = 1`, `h = 1`, `k = 5`: `p = 5` is odd with `5 ∥ 5`, `E₀ = E^{(1)}` has the good integral model
`y² = x³ + 2x² − 3x` at `5` (`Δ = 2⁸ 3²`), and its reduction `y² = x(x − 1)(x + 3)` over `𝔽₅` has
full rational two-torsion `{O, (0,0), (1,0), (2,0)}`. So the canonical component numbers satisfy the
print with `cB 5 = 4` (`edixhoven_witness_five`): the print's hypotheses are met non-vacuously and
its conclusion is a genuine, non-trivial count.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.Calibration

open ZInQ.Contrib.CloudB3RC53 WeierstrassCurve WeierstrassCurve.Affine

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The good model of `E₀ = E^{(1)}` (with `ℓ = 1`) at `5`. -/
def model5 : GoodModelAt (qtwist (Ecurve 1) ((1 : ℤ) : ℚ)) 5 :=
  goodModelE0 1 1 (by norm_num) (by norm_num)

theorem model5_red : model5.red = (⟨0, 2, 0, -3, 0⟩ : WeierstrassCurve (ZMod 5)) := by
  simp only [model5, goodModelE0, GoodModelAt.red, E0Z]
  ext <;> simp

/-- The three affine points of order two of the reduction (PROVED). -/
theorem ns5 (x : ZMod 5) (hx : x = 0 ∨ x = 1 ∨ x = 2) :
    (⟨0, 2, 0, -3, 0⟩ : WeierstrassCurve (ZMod 5)).toAffine.Nonsingular x 0 := by
  rw [Affine.nonsingular_iff, Affine.equation_iff]
  rcases hx with rfl | rfl | rfl <;> decide

/-- **`#Ẽ₀(𝔽₅)[2] = 4`** (PROVED). -/
theorem card_twoTorsion_five :
    Nat.card (AddSubgroup.torsionBy model5.red.toAffine.Point (2 : ℕ)) = 4 := by
  have := isElliptic_red model5
  have h2 : IsUnit (2 : ZMod 5) := by decide
  obtain ⟨t, ht, hcard⟩ := card_twoTorsion_eq_two_pow model5.red h2
  rw [model5_red] at hcard ⊢
  set W : WeierstrassCurve (ZMod 5) := ⟨0, 2, 0, -3, 0⟩
  have hfin : Finite (AddSubgroup.torsionBy W.toAffine.Point (2 : ℕ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have htor : ∀ x (h : W.toAffine.Nonsingular x 0),
      (Point.some x 0 h) ∈ AddSubgroup.torsionBy W.toAffine.Point (2 : ℕ) := by
    intro x h
    rw [AddSubgroup.torsionBy.nsmul_iff, two_nsmul]
    have hneg : -(Point.some x 0 h) = Point.some x 0 h := by
      rw [Point.neg_some]
      congr 1
      simp [Affine.negY, W]
    nth_rewrite 1 [← hneg]
    exact neg_add_cancel _
  let f : Fin 4 → AddSubgroup.torsionBy W.toAffine.Point (2 : ℕ) := fun i =>
    match i with
    | 0 => 0
    | 1 => ⟨_, htor 0 (ns5 0 (Or.inl rfl))⟩
    | 2 => ⟨_, htor 1 (ns5 1 (Or.inr (Or.inl rfl)))⟩
    | 3 => ⟨_, htor 2 (ns5 2 (Or.inr (Or.inr rfl)))⟩
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first
        | rfl
        | (simp [f, Subtype.ext_iff] at hij; done)
        | (revert hij; simp [f, Subtype.ext_iff]; decide)
  have hle := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, hcard] at hle
  rw [hcard]
  interval_cases t <;> first | rfl | (norm_num at hle)

/-- **A concrete non-trivial witness of the Edixhoven print** (PROVED): for `ℓ = h = 1`, `k = 5`, the
canonical component numbers satisfy `EdixhovenComponentNumber` (and its model-independent form),
and at the companion prime `5` (odd, `5 ∥ 5`, with the good model `model5`) the component number is
`4`. -/
theorem edixhoven_witness_five :
    EdixhovenComponentNumber 1 ((1 : ℤ) : ℚ) 5 (cBcanonical 1 ((1 : ℤ) : ℚ)) ∧
      EdixhovenComponentNumberIso 1 ((1 : ℤ) : ℚ) 5 (cBcanonical 1 ((1 : ℤ) : ℚ)) ∧
      (Nat.Prime 5 ∧ (5 : ℕ) ≠ 2 ∧ ((5 : ℕ) : ℤ) ∣ 5 ∧ ¬ (((5 : ℕ) : ℤ) ^ 2 ∣ 5)) ∧
      cBcanonical 1 ((1 : ℤ) : ℚ) 5 = 4 := by
  obtain ⟨h1, h2⟩ := edixhovenComponentNumber_canonical 1 ((1 : ℤ) : ℚ) 5
  refine ⟨h2, h1, ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  rw [h2 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) model5]
  exact card_twoTorsion_five

end ZInQ.Contrib.CloudB3RC53.Calibration
