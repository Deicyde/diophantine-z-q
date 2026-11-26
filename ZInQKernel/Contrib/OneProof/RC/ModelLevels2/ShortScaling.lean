import ZInQKernel.Contrib.OneProof.RC.ModelLevels.ShortIsomorphisms

/-! # Scaling the short family and its geometric generators -/

namespace WeierstrassCurve.ModelLevels

open WeierstrassCurve.Affine

variable {k : Type*} [Field k]

/-- The Weierstrass variable change whose forward action multiplies
the affine coordinates by the second and third powers of the scaling unit. -/
def shortScaling (u : kˣ) : VariableChange k :=
  ⟨u⁻¹, 0, 0, 0⟩

/-- The scaling preserves short form, and scales the two coefficients and
the discriminant by the fourth, sixth, and twelfth powers. -/
theorem shortScaling_coefficients (W : WeierstrassCurve k) [W.IsShortNF] (u : kˣ) :
    (shortScaling u • W).IsShortNF ∧
      (shortScaling u • W).a₄ = (u : k) ^ 4 * W.a₄ ∧
      (shortScaling u • W).a₆ = (u : k) ^ 6 * W.a₆ ∧
      (shortScaling u • W).Δ = (u : k) ^ 12 * W.Δ := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  all_goals
    simp [shortScaling, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, variableChange_Δ]

/-- The geometric point map at a scaling has precisely the coordinate
weights two and three. -/
theorem shortScaling_point [DecidableEq k] (W : WeierstrassCurve k) (u : kˣ)
    {x y : k} (h : W.toAffine.Nonsingular x y) :
    ∃ h' : (shortScaling u • W).toAffine.Nonsingular ((u : k) ^ 2 * x) ((u : k) ^ 3 * y),
      (Point.addEquivVariableChange W (shortScaling u)).symm (Point.some x y h) =
        Point.some _ _ h' := by
  rw [Point.coe_addEquivVariableChange_symm, Point.equivVariableChange_symm_some]
  have hs := (variableChange_nonsingular (shortScaling u • W) (shortScaling u)⁻¹ x y).mpr
    ((inv_smul_smul (shortScaling u) W).symm ▸ h)
  simpa [shortScaling, VariableChange.inv_def] using hs

/-- A scaling isomorphism preserves the exact order of the marked point
and commutes with multiplication by the natural representative of a
unit modulo the level. -/
theorem shortScaling_order_mul [DecidableEq k] (W : WeierstrassCurve k)
    (u : kˣ) (P : W.toAffine.Point) (a : ℕ) :
    let e := (Point.addEquivVariableChange W (shortScaling u)).symm
    addOrderOf (e P) = addOrderOf P ∧ e (a • P) = a • e P := by
  intro e
  exact ⟨addOrderOf_injective e.toAddMonoidHom e.injective P, map_nsmul e a P⟩

#print axioms shortScaling
#print axioms shortScaling_coefficients
#print axioms shortScaling_point
#print axioms shortScaling_order_mul

end WeierstrassCurve.ModelLevels
