import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
import ZInQKernel.Contrib.OneProof.RC.ModelLevels.Reduction
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange

/-! # Isomorphism classes of enhanced elliptic curves -/

namespace WeierstrassCurve.ModelLevels

open WeierstrassCurve.Affine

variable {k : Type*} [Field k]

/-- A change of variables between short equations over a field in which 6
is nonzero has vanishing translation and shear parameters. The scaling of
the coefficients uses the inverse of the variable-change parameter. -/
theorem short_change_parameters (W : WeierstrassCurve k) [W.IsShortNF]
    (v : VariableChange k) [(v • W).IsShortNF] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    v.r = 0 ∧ v.s = 0 ∧ v.t = 0 := by
  have hu : (↑(v.u⁻¹) : k) ≠ 0 := (v.u⁻¹ : kˣ).ne_zero
  have hs := (v • W).a₁_of_isShortNF
  simp only [variableChange_a₁, W.a₁_of_isShortNF, zero_add, mul_eq_zero, hu, h2,
    false_or] at hs
  have hr := (v • W).a₂_of_isShortNF
  simp only [variableChange_a₂, W.a₁_of_isShortNF, W.a₂_of_isShortNF, hs,
    mul_zero, zero_add, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero,
    mul_eq_zero, pow_ne_zero _ hu, h3, false_or] at hr
  have ht := (v • W).a₃_of_isShortNF
  simp only [variableChange_a₃, W.a₃_of_isShortNF, W.a₁_of_isShortNF, mul_zero, zero_add,
    mul_eq_zero, pow_ne_zero _ hu, h2, false_or] at ht
  exact ⟨hr, hs, ht⟩

/-- Equations on a scaling stabilizing the short Weierstrass chart. A zero
coefficient drops its corresponding equation. -/
theorem short_scaling_fixes_iff (W : WeierstrassCurve k) [W.IsShortNF] (u : kˣ) :
    (⟨u⁻¹, 0, 0, 0⟩ : VariableChange k) • W = W ↔
      (W.a₄ = 0 ∨ (u : k) ^ 4 = 1) ∧ (W.a₆ = 0 ∨ (u : k) ^ 6 = 1) := by
  let v : VariableChange k := ⟨u⁻¹, 0, 0, 0⟩
  have h₁ : (v • W).a₁ = W.a₁ := by simp [v, variableChange_a₁]
  have h₂ : (v • W).a₂ = W.a₂ := by simp [v, variableChange_a₂]
  have h₃ : (v • W).a₃ = W.a₃ := by simp [v, variableChange_a₃]
  have h₄ : (v • W).a₄ = (u : k) ^ 4 * W.a₄ := by simp [v, variableChange_a₄]
  have h₆ : (v • W).a₆ = (u : k) ^ 6 * W.a₆ := by simp [v, variableChange_a₆]
  have h (z c : k) : z * c = c ↔ c = 0 ∨ z = 1 := by
    by_cases hc : c = 0
    · simp [hc]
    · rw [or_iff_right hc]
      constructor
      · intro he
        exact mul_right_cancel₀ hc (he.trans (one_mul c).symm)
      · intro he
        simp [he]
  change v • W = W ↔ _
  rw [WeierstrassCurve.ext_iff]
  simp [h₁, h₂, h₃, h₄, h₆, h]

/-- The two exceptional (j)-values distinguish which stabilizer equation
remains, when 2 and 3 are nonzero. -/
theorem short_exceptional_j (W : WeierstrassCurve k) [W.IsElliptic] [W.IsShortNF]
    (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) :
    (W.j = 0 ↔ W.a₄ = 0) ∧ (W.j = 1728 ↔ W.a₆ = 0) := by
  have hΔ : (4 * W.a₄ ^ 3 + 27 * W.a₆ ^ 2) ≠ 0 := by
    intro hz
    have h := W.Δ'.ne_zero
    rw [coe_Δ', Δ_of_isShortNF, hz, mul_zero] at h
    exact h rfl
  have h6912 : (6912 : k) ≠ 0 := by
    rw [show (6912 : k) = 2 ^ 8 * 3 ^ 3 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  have h46656 : (46656 : k) ≠ 0 := by
    rw [show (46656 : k) = 2 ^ 6 * 3 ^ 6 by norm_num]
    exact mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3)
  rw [W.j_of_isShortNF]
  constructor
  · simp [div_eq_zero_iff, hΔ, h6912]
  · rw [div_eq_iff hΔ]
    constructor
    · intro hj
      have hz : (46656 : k) * W.a₆ ^ 2 = 0 := by linear_combination -hj
      simpa [h46656] using hz
    · intro ha
      rw [ha]
      ring

/-- The short chart stabilizer is the group of roots of unity of order
6 at `j = 0`, of order 4 at `j = 1728`, and of order 2 elsewhere.
Any stabilizer of enhanced level data is a subgroup of this chart stabilizer. -/
theorem short_stabilizer (W : WeierstrassCurve k) [W.IsElliptic] [W.IsShortNF]
    [DecidableEq k] (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0) (u : kˣ) :
    (⟨u⁻¹, 0, 0, 0⟩ : VariableChange k) • W = W ↔
      if W.j = 0 then (u : k) ^ 6 = 1
      else if W.j = 1728 then (u : k) ^ 4 = 1
      else (u : k) ^ 2 = 1 := by
  classical
  obtain ⟨hJ₀, hJ₁⟩ := short_exceptional_j W h2 h3
  have hne : ¬ (W.a₄ = 0 ∧ W.a₆ = 0) := by
    rintro ⟨h₄, h₆⟩
    have h := W.Δ'.ne_zero
    rw [coe_Δ', Δ_of_isShortNF, h₄, h₆] at h
    simp at h
  rw [short_scaling_fixes_iff]
  by_cases h₄ : W.a₄ = 0
  · rw [if_pos (hJ₀.mpr h₄)]
    have h₆ : W.a₆ ≠ 0 := fun hz => hne ⟨h₄, hz⟩
    simp [h₄, h₆]
  have hj₀ : W.j ≠ 0 := h₄ ∘ hJ₀.mp
  by_cases h₆ : W.a₆ = 0
  · rw [if_neg hj₀, if_pos (hJ₁.mpr h₆)]
    simp [h₄, h₆]
  have hj₁ : W.j ≠ 1728 := h₆ ∘ hJ₁.mp
  rw [if_neg hj₀, if_neg hj₁]
  simp only [h₄, h₆, false_or]
  constructor
  · rintro ⟨h₄', h₆'⟩
    rwa [show (u : k) ^ 6 = (u : k) ^ 4 * (u : k) ^ 2 by ring, h₄', one_mul] at h₆'
  · intro h
    constructor
    · rw [show 4 = 2 * 2 by decide, pow_mul, h, one_pow]
    · rw [show 6 = 2 * 3 by decide, pow_mul, h, one_pow]

/-- A Weierstrass presentation of an elliptic curve and an actual cyclic
subgroup of order (N) in its point group. -/
structure EnhancedCurve (k : Type*) [Field k] [DecidableEq k] (N : ℕ) where
  equation : WeierstrassCurve k
  elliptic : equation.IsElliptic
  subgroup : CyclicSubgroups equation.toAffine.Point N

/-- Isomorphism classes of elliptic curves with their cyclic subgroup,
using the action of Weierstrass changes of variables on points. -/
def PairClasses (k : Type*) [Field k] [DecidableEq k] (N : ℕ) :=
  Quot fun (A B : EnhancedCurve k N) => ∃ v : VariableChange k, ∃ h : v • A.equation = B.equation,
    (Affine.Point.addEquivVariableChange A.equation v).symm.mapAddSubgroup A.subgroup.1 =
      h.symm ▸ B.subgroup.1

#print axioms short_change_parameters
#print axioms short_scaling_fixes_iff
#print axioms short_exceptional_j
#print axioms short_stabilizer
#print axioms PairClasses

end WeierstrassCurve.ModelLevels
