import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_Affine_GenusOnePlaceGate_ext_of_isCentred
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_Affine_CoordinateRing_isDedekindDomain
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange

/-! # The function-field map of a Weierstrass variable change, with its point formula

**ON THE SPOT (c).** For a Weierstrass curve `W` and a variable change `C`, the vendored
function-field map `mrtw60aVCFunHom : W.FunctionField →ₐ (C • W).FunctionField` sends
`X ↦ u²X + r` and `Y ↦ u³Y + u²sX + t` (the vendored existence theorem
`nonempty_functionField_algEquiv_of_variableChange` only states `Nonempty`). We prove that its
restriction of places is the actual point map `Point.addEquivVariableChange W C`, for every
pair of centred place gates (`restrictAlong_vcFunHom`): the places transported along the map form
a centred gate on `W`, and centred gates are unique
(`GenusOnePlaceGate.ext_of_isCentred`, vendored). No characteristic assumption is made. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ZInQ.Manuscript.RC.ModelGeneric6

open AlgebraicCurve WeierstrassCurve WeierstrassCurve.Affine Polynomial

/-- An element of a valuation subring's non-units: zero, or with inverse outside. -/
theorem mem_nonunits_iff' {F : Type*} [Field F] (A : ValuationSubring F) (x : F) :
    x ∈ A.nonunits ↔ x = 0 ∨ x⁻¹ ∉ A := by
  rw [ValuationSubring.mem_nonunits_iff]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : A.valuation x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, or_iff_right hx,
      inv_le_one₀ (zero_lt_iff.mpr h0), not_le]

theorem mem_nonunits_comap {F F' : Type*} [Field F] [Field F'] (φ : F →+* F')
    (A : ValuationSubring F') (x : F) :
    x ∈ (A.comap φ).nonunits ↔ φ x ∈ A.nonunits := by
  rw [mem_nonunits_iff', mem_nonunits_iff', ValuationSubring.mem_comap, map_inv₀,
    map_eq_zero]

theorem add_mem_nonunits {F : Type*} [Field F] (A : ValuationSubring F) {a b : F}
    (ha : a ∈ A.nonunits) (hb : b ∈ A.nonunits) : a + b ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at *
  exact Valuation.map_add_lt _ ha hb

theorem mul_mem_nonunits {F : Type*} [Field F] (A : ValuationSubring F) {c a : F}
    (hc : c ∈ A) (ha : a ∈ A.nonunits) : c * a ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff] at *
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' ((ValuationSubring.valuation_le_one_iff A c).2 hc)) ha

variable {k : Type*} [Field k] [DecidableEq k]

/-- The vendored function-field map of a variable change: `X ↦ u²X + r`, `Y ↦ u³Y + u²sX + t`.
It is the pull-back along the point map `(C • W)(k) → W(k)`. -/
def vcFunHom (W : WeierstrassCurve k) (C : VariableChange k) :
    W.toAffine.FunctionField →ₐ[k] (C • W).toAffine.FunctionField :=
  P2MW.S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.FLT.Mrtw60aVCPlaceSeamS3.mrtw60aVCFunHom
    (C := C) (W := W.toAffine) (V := (C • W).toAffine) rfl

/-- The inverse map, from the vendored inverse. -/
def vcFunHomInv (W : WeierstrassCurve k) (C : VariableChange k) :
    (C • W).toAffine.FunctionField →ₐ[k] W.toAffine.FunctionField :=
  P2MW.S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.FLT.Mrtw60aVCPlaceSeamS3.mrtw60aVCFunHomInv
    (C := C) (W := W.toAffine) (V := (C • W).toAffine) rfl

theorem vcFunHomInv_comp (W : WeierstrassCurve k) (C : VariableChange k) :
    (vcFunHomInv W C).comp (vcFunHom W C) = AlgHom.id k _ :=
  P2MW.S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.FLT.Mrtw60aVCPlaceSeamS3.mrtw60a_funHomInv_comp_funHom
    (C := C) (W := W.toAffine) (V := (C • W).toAffine) rfl

theorem vcFunHom_comp_inv (W : WeierstrassCurve k) (C : VariableChange k) :
    (vcFunHom W C).comp (vcFunHomInv W C) = AlgHom.id k _ :=
  P2MW.S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.FLT.Mrtw60aVCPlaceSeamS3.mrtw60a_funHom_comp_funHomInv
    (C := C) (W := W.toAffine) (V := (C • W).toAffine) rfl

theorem vcFunHom_isIntegral (W : WeierstrassCurve k) (C : VariableChange k) :
    (vcFunHom W C).toRingHom.IsIntegral := by
  apply RingHom.isIntegral_of_surjective
  intro z
  refine ⟨vcFunHomInv W C z, ?_⟩
  exact AlgHom.congr_fun (vcFunHom_comp_inv W C) z

theorem vcFunHomInv_isIntegral (W : WeierstrassCurve k) (C : VariableChange k) :
    (vcFunHomInv W C).toRingHom.IsIntegral := by
  apply RingHom.isIntegral_of_surjective
  intro z
  refine ⟨vcFunHom W C z, ?_⟩
  exact AlgHom.congr_fun (vcFunHomInv_comp W C) z

theorem vcFunHom_finiteAlong (W : WeierstrassCurve k) (C : VariableChange k) :
    FiniteAlong k (vcFunHom W C) := by
  change RingHom.Finite (vcFunHom W C).toRingHom
  apply RingHom.Finite.of_surjective
  intro z
  exact ⟨vcFunHomInv W C z, AlgHom.congr_fun (vcFunHom_comp_inv W C) z⟩

theorem vcFunHom_X (W : WeierstrassCurve k) (C : VariableChange k) :
    vcFunHom W C (polyToFunctionField W.toAffine X) =
      algebraMap k _ ((C.u : k) ^ 2) * polyToFunctionField (C • W).toAffine X +
        algebraMap k _ C.r := by
  unfold vcFunHom
  rw [P2MW.S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.FLT.Mrtw60aVCPlaceSeamS3.mrtw60aVCFunHom_X,
    P2MW.S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.FLT.Mrtw60aVCPlaceSeamS1.mrtw60a_xFwd_shape]

theorem vcFunHom_Y (W : WeierstrassCurve k) (C : VariableChange k) :
    vcFunHom W C (yCoord W.toAffine) =
      algebraMap k _ ((C.u : k) ^ 3) * yCoord (C • W).toAffine +
        algebraMap k _ ((C.u : k) ^ 2 * C.s) * polyToFunctionField (C • W).toAffine X +
        algebraMap k _ C.t := by
  unfold vcFunHom
  exact (P2MW.S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.FLT.Mrtw60aVCPlaceSeamS3.mrtw60aVCFunHom_yGen _).trans
    (P2MW.S_WeierstrassCurve_nonempty_functionField_algEquiv_of_variableChange.FLT.Mrtw60aVCPlaceSeamS1.mrtw60a_yFwd_shape _ _)

theorem algebraMap_C_C (W : WeierstrassCurve k) (a : k) :
    algebraMap k W.toAffine.CoordinateRing a = CoordinateRing.mk W.toAffine (C (C a)) := by
  rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_apply,
    Algebra.algebraMap_self_apply]
  rfl

theorem algebraMap_XClass (W : WeierstrassCurve k) (x : k) :
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (CoordinateRing.XClass W.toAffine x) =
      polyToFunctionField W.toAffine X - algebraMap k _ x := by
  rw [CoordinateRing.XClass, polyToFunctionField_apply,
    IsScalarTower.algebraMap_apply k W.toAffine.CoordinateRing W.toAffine.FunctionField,
    algebraMap_C_C, ← map_sub, map_sub, map_sub]
  rfl

theorem algebraMap_YClass (W : WeierstrassCurve k) (y : k) :
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
        (CoordinateRing.YClass W.toAffine (Polynomial.C y)) =
      yCoord W.toAffine - algebraMap k _ y := by
  rw [CoordinateRing.YClass, yCoord,
    IsScalarTower.algebraMap_apply k W.toAffine.CoordinateRing W.toAffine.FunctionField,
    algebraMap_C_C, ← map_sub, map_sub]

section Gate

variable [IsAlgClosed k] (W : WeierstrassCurve k) [W.IsElliptic] (C : VariableChange k)
  [(C • W).IsElliptic]

/-- Restriction of places along the function-field map, as a bijection. -/
def vcPlaceEquiv : Place k (C • W).toAffine.FunctionField ≃ Place k W.toAffine.FunctionField where
  toFun w := w.restrictAlong (vcFunHom W C) (vcFunHom_isIntegral W C)
  invFun w := w.restrictAlong (vcFunHomInv W C) (vcFunHomInv_isIntegral W C)
  left_inv w := by
    have h := Place.restrictAlong_restrictAlong (vcFunHomInv W C) (vcFunHom W C)
      (vcFunHomInv_isIntegral W C) (vcFunHom_isIntegral W C)
      (by rw [vcFunHom_comp_inv]; exact
        P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.WeierstrassCurve.Affine.IsogenyEndDatum.isIntegral_algHomId _) w
    simp only at h ⊢
    rw [h]
    convert P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.WeierstrassCurve.Affine.IsogenyEndDatum.restrictAlong_algHomId _ w
      using 2
    exact vcFunHom_comp_inv W C
  right_inv w := by
    have h := Place.restrictAlong_restrictAlong (vcFunHom W C) (vcFunHomInv W C)
      (vcFunHom_isIntegral W C) (vcFunHomInv_isIntegral W C)
      (by rw [vcFunHomInv_comp]; exact
        P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.WeierstrassCurve.Affine.IsogenyEndDatum.isIntegral_algHomId _) w
    simp only at h ⊢
    rw [h]
    convert P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.WeierstrassCurve.Affine.IsogenyEndDatum.restrictAlong_algHomId _ w
      using 2
    exact vcFunHomInv_comp W C

/-- The gate on `W` transported from a gate on `C • W` along the variable change. -/
@[instance_reducible] def transportGate (gW : GenusOnePlaceGate W.toAffine)
    (gV : GenusOnePlaceGate (C • W).toAffine) : GenusOnePlaceGate W.toAffine where
  pointEquivPlace :=
    (Point.addEquivVariableChange W C).symm.toEquiv.trans
      ((@pointEquivPlace k _ _ gV).trans (vcPlaceEquiv W C))
  deg_eq_one := gW.deg_eq_one

theorem transportGate_isCentred (gW : GenusOnePlaceGate W.toAffine)
    (gV : GenusOnePlaceGate (C • W).toAffine)
    (hV : @GenusOnePlaceGate.IsCentred k _ (C • W).toAffine gV) :
    @GenusOnePlaceGate.IsCentred k _ W.toAffine (transportGate W C gW gV) := by
  letI := gV
  have key : ∀ (x y : k) (h : W.toAffine.Nonsingular x y), ∃ x' y' h',
      (Point.addEquivVariableChange W C).symm (Point.some x y h) = Point.some x' y' h' ∧
      x = (C.u : k) ^ 2 * x' + C.r ∧ y = (C.u : k) ^ 3 * y' + (C.u : k) ^ 2 * C.s * x' + C.t := by
    intro x y h
    rcases hP : (Point.addEquivVariableChange W C).symm (Point.some x y h) with _ | ⟨x', y', h'⟩
    · exfalso
      have : Point.some x y h = 0 := by
        rw [← AddEquiv.apply_symm_apply (Point.addEquivVariableChange W C) (Point.some x y h), hP]
        exact map_zero _
      cases this
    · refine ⟨x', y', h', rfl, ?_⟩
      have := congrArg (Point.addEquivVariableChange W C) hP
      rw [AddEquiv.apply_symm_apply, Point.coe_addEquivVariableChange,
        Point.equivVariableChange_some] at this
      exact Point.some.inj this
  have hcomap : ∀ (P : (C • W).toAffine.Point) (f : W.toAffine.FunctionField),
      f ∈ (vcPlaceEquiv W C (placeOfPoint P)).toValuationSubring.nonunits ↔
        vcFunHom W C f ∈ (placeOfPoint P).toValuationSubring.nonunits := fun P f =>
    mem_nonunits_comap (vcFunHom W C).toRingHom _ f
  refine @GenusOnePlaceGate.IsCentred.mk k _ W.toAffine (transportGate W C gW gV) ?_ ?_
  · intro x y h
    change _ ∈ (vcPlaceEquiv W C (placeOfPoint
      ((Point.addEquivVariableChange W C).symm (Point.some x y h)))).toValuationSubring.nonunits
    obtain ⟨x', y', h', hP, hx, -⟩ := key x y h
    rw [hP, hcomap]
    have hXc : vcFunHom W C (algebraMap _ _ (CoordinateRing.XClass W.toAffine x)) =
        algebraMap k _ ((C.u : k) ^ 2) *
          algebraMap _ _ (CoordinateRing.XClass (C • W).toAffine x') := by
      rw [algebraMap_XClass, algebraMap_XClass, map_sub, vcFunHom_X, AlgHom.commutes, hx,
        map_add, map_mul]
      ring
    rw [hXc]
    exact mul_mem_nonunits _ ((placeOfPoint _).algebraMap_mem' _)
      (GenusOnePlaceGate.IsCentred.XClass_mem_nonunits x' y' h')
  · intro x y h
    change _ ∈ (vcPlaceEquiv W C (placeOfPoint
      ((Point.addEquivVariableChange W C).symm (Point.some x y h)))).toValuationSubring.nonunits
    obtain ⟨x', y', h', hP, -, hy⟩ := key x y h
    rw [hP, hcomap]
    have hYc : vcFunHom W C (algebraMap _ _ (CoordinateRing.YClass W.toAffine (Polynomial.C y))) =
        algebraMap k _ ((C.u : k) ^ 3) *
          algebraMap _ _ (CoordinateRing.YClass (C • W).toAffine (Polynomial.C y')) +
        algebraMap k _ ((C.u : k) ^ 2 * C.s) *
          algebraMap _ _ (CoordinateRing.XClass (C • W).toAffine x') := by
      rw [algebraMap_YClass, algebraMap_YClass, algebraMap_XClass, map_sub, vcFunHom_Y,
        AlgHom.commutes, hy]
      simp only [map_add, map_mul, map_pow]
      ring
    rw [hYc]
    exact add_mem_nonunits _
      (mul_mem_nonunits _ ((placeOfPoint _).algebraMap_mem' _)
        (GenusOnePlaceGate.IsCentred.YClass_mem_nonunits x' y' h'))
      (mul_mem_nonunits _ ((placeOfPoint _).algebraMap_mem' _)
        (GenusOnePlaceGate.IsCentred.XClass_mem_nonunits x' y' h'))

/-- **ON THE SPOT (c): the point formula of the variable-change function-field map.** For all
centred place gates on `W` and on `C • W`, the restriction along `vcFunHom W C` of the place of
`P ∈ (C • W)(k)` is the place of `Point.addEquivVariableChange W C P ∈ W(k)`. -/
theorem restrictAlong_vcFunHom [gW : GenusOnePlaceGate W.toAffine]
    [hW : GenusOnePlaceGate.IsCentred W.toAffine]
    [gV : GenusOnePlaceGate (C • W).toAffine] [hV : GenusOnePlaceGate.IsCentred (C • W).toAffine]
    (P : (C • W).toAffine.Point) :
    (placeOfPoint P).restrictAlong (vcFunHom W C) (vcFunHom_isIntegral W C) =
      placeOfPoint (Point.addEquivVariableChange W C P) := by
  haveI := CoordinateRing.isDedekindDomain W
  have hext := GenusOnePlaceGate.ext_of_isCentred (transportGate W C gW gV) gW
    (transportGate_isCentred W C gW gV hV) hW
  have h1 : @placeOfPoint k _ _ (transportGate W C gW gV)
      (Point.addEquivVariableChange W C P) =
      (placeOfPoint P).restrictAlong (vcFunHom W C) (vcFunHom_isIntegral W C) := by
    change vcPlaceEquiv W C (placeOfPoint ((Point.addEquivVariableChange W C).symm
      (Point.addEquivVariableChange W C P))) = _
    rw [AddEquiv.symm_apply_apply]
    rfl
  rw [← h1, hext]

end Gate

#print axioms restrictAlong_vcFunHom

end ZInQ.Manuscript.RC.ModelGeneric6
