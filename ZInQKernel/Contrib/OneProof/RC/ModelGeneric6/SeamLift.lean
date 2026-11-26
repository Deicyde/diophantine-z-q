import ZInQKernel.Contrib.OneProof.RC.ModelGeneric6.VariableChangeSeam
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric4.LatticeQuotient
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.PairIsomorphisms

/-! # Seams between complex curves lift to `z ↦ αz`

* `isSeam_changePoints`, `isSeam_changePoints_symm`: the point isomorphism `changePoints` of a
  variable change, and its inverse, are seams (`ModelGeneric4.IsSeam`) for the explicit
  variable-change function-field maps (`vcFunHomInv`, `vcFunHom`; ON THE SPOT (c), see
  `VariableChangeSeam`).
* `isSeam_comp'`: seams compose.
* `exists_lift_of_seam`: every seam `f` between the period curves of two period pairs lifts to a
  homothety, `f (toPoint z) = toPoint (α z)`. This is the argument of
  `ModelGeneric4.j_eq_analyticJN_of_seam`, now for the seam itself: the vendored lift
  `exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint` and the vendored
  linearity of lattice-periodic entire maps. Background: Silverman, *The Arithmetic of
  Elliptic Curves*, 2nd ed., 2009, VI.3.6 and VI.4.1 (UNVERIFIED). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Manuscript.RC.ModelGeneric6

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.ModelLevels
open WeierstrassCurve.ModelLevels.ModelGeneric4

section Seams

variable {k : Type} [Field k] [DecidableEq k] [IsAlgClosed k] [CharZero k]

/-- Seams compose (the generic4 lemma is private; this is the same four-line argument). -/
theorem isSeam_comp' {U V W : WeierstrassCurve k} [U.IsElliptic] [V.IsElliptic]
    [W.IsElliptic] (ι₁ : V.toAffine.FunctionField →ₐ[k] U.toAffine.FunctionField)
    (hι₁ : ι₁.toRingHom.IsIntegral) (f₁ : U.toAffine.Point →+ V.toAffine.Point)
    (ι₂ : W.toAffine.FunctionField →ₐ[k] V.toAffine.FunctionField)
    (hι₂ : ι₂.toRingHom.IsIntegral) (f₂ : V.toAffine.Point →+ W.toAffine.Point)
    (h₁ : IsSeam ι₁ hι₁ f₁) (h₂ : IsSeam ι₂ hι₂ f₂) (hι : (ι₁.comp ι₂).toRingHom.IsIntegral) :
    IsSeam (ι₁.comp ι₂) hι (f₂.comp f₁) := by
  intro P
  rw [← Place.restrictAlong_restrictAlong ι₂ ι₁ hι₂ hι₁ hι, h₁ P, h₂ (f₁ P)]
  rfl

/-- `changePoints` of a variable change is a seam, for the explicit inverse variable-change
function-field map. -/
theorem isSeam_changePoints (E W : WeierstrassCurve k) [E.IsElliptic] [W.IsElliptic]
    (v : VariableChange k) (h : v • E = W) :
    ∃ (ι : W.toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧
        IsSeam ι hι (changePoints E W v h).toAddMonoidHom := by
  subst h
  refine ⟨vcFunHomInv E v, vcFunHomInv_isIntegral E v, ?_, fun P => ?_⟩
  · change RingHom.Finite (vcFunHomInv E v).toRingHom
    apply RingHom.Finite.of_surjective
    intro z
    exact ⟨vcFunHom E v z, AlgHom.congr_fun (vcFunHomInv_comp E v) z⟩
  · letI := gate E
    haveI := gate_isCentred E
    letI := gate (v • E)
    haveI := gate_isCentred (v • E)
    have h1 := restrictAlong_vcFunHom E v ((Point.addEquivVariableChange E v).symm P)
    rw [AddEquiv.apply_symm_apply] at h1
    change (vcPlaceEquiv E v) (placeOfPoint _) = _ at h1
    have h2 := congrArg (vcPlaceEquiv E v).symm h1
    rw [Equiv.symm_apply_apply] at h2
    change Place.restrictAlong _ (vcFunHomInv_isIntegral E v) (placeOfPoint P) =
      placeOfPoint ((Point.addEquivVariableChange E v).symm P)
    exact h2.symm

/-- The inverse of `changePoints` is a seam, for the explicit variable-change function-field
map. -/
theorem isSeam_changePoints_symm (E W : WeierstrassCurve k) [E.IsElliptic] [W.IsElliptic]
    (v : VariableChange k) (h : v • E = W) :
    ∃ (ι : E.toAffine.FunctionField →ₐ[k] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧
        IsSeam ι hι (changePoints E W v h).symm.toAddMonoidHom := by
  subst h
  refine ⟨vcFunHom E v, vcFunHom_isIntegral E v, vcFunHom_finiteAlong E v, fun P => ?_⟩
  letI := gate E
  haveI := gate_isCentred E
  letI := gate (v • E)
  haveI := gate_isCentred (v • E)
  exact restrictAlong_vcFunHom E v P

end Seams

section Lift

/-- **Seams between period curves lift to homotheties.** If `f` is a seam from the period
curve of `L₁` to the period curve of `L₂`, there is `α` with `f (toPoint z) = toPoint (α z)`
for all `z`. -/
theorem exists_lift_of_seam (L₁ L₂ : PeriodPair)
    [L₁.weierstrassCurve.IsElliptic] [L₂.weierstrassCurve.IsElliptic]
    (ι : L₂.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ] L₁.weierstrassCurve.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι)
    (f : L₁.weierstrassCurve.toAffine.Point →+ L₂.weierstrassCurve.toAffine.Point)
    (hseam : IsSeam ι hι f) :
    ∃ α : ℂ, ∀ z : ℂ, f (L₁.toPoint L₁.discriminant_ne_zero z) =
      L₂.toPoint L₂.discriminant_ne_zero (α * z) := by
  have hL₁ := L₁.discriminant_ne_zero
  have hL₂ := L₂.discriminant_ne_zero
  letI := gate L₁.weierstrassCurve
  haveI := gate_isCentred L₁.weierstrassCurve
  haveI := gate_abel L₁.weierstrassCurve
  letI := gate L₂.weierstrassCurve
  haveI := gate_isCentred L₂.weierstrassCurve
  haveI := gate_abel L₂.weierstrassCurve
  have hN := P2MW.S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.F4Proof.normFormulaAlong_of_charZero
    ι hfin
  obtain ⟨F, hF, hF0, hFz⟩ :=
    PeriodPair.exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint
      L₁ L₂ hL₁ hL₂ ι hι hfin hN
  have hpush : ∀ P, pointMapOfPushforward ι hι hfin hN P = f P :=
    pointMapOfPushforward_eq_of_seam ι hι hfin hN f f.map_zero hseam
  have hper : ∀ l ∈ L₁.lattice, ∀ z, F (z + l) - F z ∈ L₂.lattice := by
    intro l hl z
    rw [← toPoint_eq_toPoint_iff L₂ hL₂, hFz, hFz,
      (toPoint_eq_toPoint_iff L₁ hL₁ (z + l) z).2 (by simpa using hl)]
  obtain ⟨α, -, hα⟩ :=
    P2MW.S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient.PeriodPair.exists_smul_mem_and_apply_eq_of_forall_sub_mem
      L₁ L₂ hF hper
  refine ⟨α, fun z => ?_⟩
  rw [← hpush, ← hFz, hα, (L₂.isUniformization_toPoint hL₂).1, L₂.toPoint_of_mem hL₂ hF0,
    zero_add]

end Lift

#print axioms isSeam_comp'
#print axioms isSeam_changePoints
#print axioms isSeam_changePoints_symm
#print axioms exists_lift_of_seam

end ZInQ.Manuscript.RC.ModelGeneric6
