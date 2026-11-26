import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.FieldComparison
import ZInQKernel.Contrib.OneProof.RC.X0Model3.AffineEval
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-! # The affine pinning of the rational open -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric2

open AlgebraicGeometry CategoryTheory LeafModCurves ModelGeneric ModularCurve
open ZInQ.Contrib.CloudW07JacobiansCurves
open ZInQ.Manuscript.RC
open scoped TensorProduct
open private finiteChart_affine from ZInQKernel.Contrib.OneProof.RC.X0Model3.AffineEval

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 60000

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

private theorem rationalAlgebra_isDomain : IsDomain (Y0RationalAlgebra h₂) := by
  letI := genericJField h₂
  exact Function.Injective.isDomain (Y0RationalGenericJInclusion h₂)
    (Y0RationalGenericJInclusion_injective h₂)

private theorem rationalAlgebra_isIntegrallyClosed : IsIntegrallyClosed (Y0RationalAlgebra h₂) := by
  letI := rationalAlgebra_isDomain h₂
  exact IsIntegrallyClosed.of_localization_maximal fun p _ hp => by
    letI := hp.isPrime
    exact (Y0RationalAlgebra_normal h₂ p).2

private theorem genericJ_isFractionRing :
    letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
    IsFractionRing (Y0RationalAlgebra h₂) (Y0RationalGenericJ h₂) := by
  let P := Polynomial ℚ
  let B : Type := Y0RationalAlgebra h₂
  let E := Y0RationalGenericJ h₂
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  letI : Field E := genericJField h₂
  letI : IsDomain B := rationalAlgebra_isDomain h₂
  let S := Algebra.algebraMapSubmonoid B (nonZeroDivisors P)
  letI : IsLocalization S E :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors P) Qj).mpr inferInstance
  letI : Module.IsTorsionFree P B := Y0RationalAlgebra_j_torsionFree h₂
  have h₁ : S ≤ nonZeroDivisors B :=
    map_le_nonZeroDivisors_of_injective (algebraMap P B)
      (FaithfulSMul.algebraMap_injective P B) le_rfl
  have h₂' : ∀ b ∈ nonZeroDivisors B, IsUnit (algebraMap B E b) := by
    intro b hb
    have hb' : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    have hinj : Function.Injective (algebraMap B E) := Y0RationalGenericJInclusion_injective h₂
    have hne : algebraMap B E b ≠ 0 := fun hz =>
      hb' (hinj (hz.trans ((algebraMap B E).map_zero.symm)))
    exact hne.isUnit
  exact IsLocalization.of_le S (nonZeroDivisors B) h₁ h₂'

private noncomputable abbrev finiteJChart := NormalModel.chart 0

private theorem finiteJChart_algebraMap (f : Polynomial ℚ) :
    letI := NormalModel.algSecF (modularFunctionField N) finiteJChart
    algebraMap Γ(NormalModel.P, finiteJChart) (modularFunctionField N)
      (ProjectiveLine.polyEquivChart ℚ 0 f) =
    algebraMap Qj (modularFunctionField N) (algebraMap (Polynomial ℚ) Qj f) := by
  let := NormalModel.algSecF (modularFunctionField N) finiteJChart
  have : IsFractionRing Γ(NormalModel.P, finiteJChart) NormalModel.P.functionField :=
    functionField_isFractionRing_of_isAffineOpen _ _ (NormalModel.isAffineOpen_chart 0)
  change _ = _
  rw [show algebraMap Γ(NormalModel.P, finiteJChart) (modularFunctionField N) _ =
    NormalModel.φ (modularFunctionField N)
      (NormalModel.P.germToFunctionField finiteJChart (ProjectiveLine.polyEquivChart ℚ 0 f))
    from NormalModel.εIso_app_apply (modularFunctionField N) finiteJChart _]
  have hr : NormalModel.ratFuncEquiv (algebraMap (Polynomial ℚ) Qj f) =
      NormalModel.P.germToFunctionField finiteJChart (ProjectiveLine.polyEquivChart ℚ 0 f) :=
    IsFractionRing.ringEquivOfRingEquiv_algebraMap (ProjectiveLine.polyEquivChart ℚ 0) f
  rw [← hr]
  change algebraMap Qj (modularFunctionField N)
    (NormalModel.ratFuncEquiv.symm (NormalModel.ratFuncEquiv _)) = _
  rw [RingEquiv.symm_apply_apply]

/-- The fixed finite chart and the pinned rational ring are the same integral
closure over the affine j-line. The equivalence preserves every function on that line. -/
noncomputable def rationalChartSections :
    { e : Γ(X0Model.curve N, X0Model3.finiteChart N) ≃+* Y0RationalAlgebra h₂ //
      ∀ f : Polynomial ℚ, e ((X0Model2.jProjection N).app finiteJChart
        (ProjectiveLine.polyEquivChart ℚ 0 f)) = Y0RationalJMap h₂ f } := by
  let data := Classical.choice (nonempty_modularPolynomialData N)
  let P := Polynomial ℚ
  let B := Y0RationalAlgebra h₂
  let E := Y0RationalGenericJ h₂
  let F := modularFunctionField N
  let C := Γ(NormalModel.P, finiteJChart)
  let p := ProjectiveLine.polyEquivChart ℚ 0
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  letI : Field E := genericJField h₂
  letI : IsDomain B := rationalAlgebra_isDomain h₂
  letI : IsIntegrallyClosed B := rationalAlgebra_isIntegrallyClosed h₂
  letI : IsFractionRing B E := genericJ_isFractionRing h₂
  let e := genericModularFieldEquiv h₂ data
  letI : Algebra B F := (e.toRingHom.comp (algebraMap B E)).toAlgebra
  let e' : E ≃ₐ[B] F := AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun _ => rfl
  letI : IsFractionRing B F := IsFractionRing.of_algEquiv e'
  letI : Algebra C B := ((Y0RationalJMap h₂).toRingHom.comp p.symm.toRingHom).toAlgebra
  have hFinite : (Y0RationalJMap h₂).toRingHom.Finite :=
    RingHom.finite_algebraMap.mpr (Y0RationalJMap_finite h₂)
  letI : Module.Finite C B := RingHom.finite_algebraMap.mp
    (hFinite.comp (RingHom.Finite.of_surjective _ p.symm.surjective))
  letI := NormalModel.algSecF F finiteJChart
  letI : IsScalarTower C B F := IsScalarTower.of_algebraMap_eq fun c => by
    obtain ⟨f, rfl⟩ := p.surjective c
    rw [finiteJChart_algebraMap (N := N), ← e.commutes]
    change _ = e (algebraMap B E (Y0RationalJMap h₂ (p.symm (p f))))
    rw [RingEquiv.symm_apply_apply]
    congr 1
    exact (Algebra.TensorProduct.includeRight (R := P) (A := Qj) (B := B)).commutes f |>.symm
  letI : IsIntegralClosure B B F :=
    (isIntegrallyClosed_iff_isIntegralClosure F).mp (rationalAlgebra_isIntegrallyClosed h₂)
  letI : IsIntegralClosure B C F := IsIntegralClosure.of_isIntegrallyClosedIn
  letI := ((NormalModel.f F).app finiteJChart).hom.toAlgebra
  let eC := (NormalModel.εAlg F finiteJChart).mapIntegralClosure
  let eNorm := ((NormalModel.f F).normalizationObjIso (NormalModel.isAffineOpen_chart 0))
  let eB := IsIntegralClosure.equiv C B F (integralClosure C F)
  refine ⟨(eNorm.commRingCatIsoToRingEquiv.trans eC.toRingEquiv).trans eB.symm.toRingEquiv, ?_⟩
  intro f
  apply eB.injective
  change eB (eB.symm (eC (eNorm.hom ((X0Model2.jProjection N).app finiteJChart (p f))))) =
    eB (Y0RationalJMap h₂ f)
  rw [eB.apply_symm_apply, show (X0Model2.jProjection N).app finiteJChart = _ from
    (NormalModel.f F).fromNormalization_app (NormalModel.isAffineOpen_chart 0)]
  simp only [CommRingCat.comp_apply]
  let z : integralClosure C Γ(Spec (CommRingCat.of F), NormalModel.f F ⁻¹ᵁ finiteJChart) :=
    algebraMap C _ (p f)
  change eC (eNorm.hom (eNorm.inv z)) = _
  have hNorm : eNorm.hom (eNorm.inv z) = z := by
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom eNorm.inv_hom_id) z
  rw [hNorm]
  change eC (algebraMap C _ (p f)) = _
  rw [eC.commutes, ← eB.commutes (p f)]
  change eB ((Y0RationalJMap h₂) (p.symm (p f))) = _
  rw [RingEquiv.symm_apply_apply]

/-- The pinned rational scheme as an open subscheme of the fixed compact model. -/
noncomputable def rationalOpenImmersion : (Y0Rational h₂).left ⟶ X0Model.curve N :=
  Spec.map (CommRingCat.ofHom (rationalChartSections h₂).val.toRingHom) ≫
    (finiteChart_affine N).fromSpec

theorem rationalOpenImmersion_isOpen : IsOpenImmersion (rationalOpenImmersion h₂) := by
  unfold rationalOpenImmersion
  have e : IsIso (Spec.map (CommRingCat.ofHom (rationalChartSections h₂).val.toRingHom)) :=
    (Scheme.Spec.mapIso (rationalChartSections h₂).val.toCommRingCatIso.op).isIso_hom
  infer_instance

/-- The cusps of the fixed compact curve are the points over j = ∞. -/
def cusps (N : ℕ) [NeZero N] : Set (X0Model.curve N) :=
  {x | X0Model2.jProjection N x ∉ (finiteJChart : Set NormalModel.P)}

/-- The image of the pinned open is the actual finite chart. -/
theorem rationalOpenImmersion_range :
    Set.range (rationalOpenImmersion h₂) = X0Model3.finiteChart N := by
  let e := Scheme.Spec.mapIso (rationalChartSections h₂).val.toCommRingCatIso.op
  change Set.range (fun x => (finiteChart_affine N).fromSpec (e.hom x)) = _
  exact (e.hom.surjective.range_comp _).trans (finiteChart_affine N).range_fromSpec

theorem rationalOpenImmersion_range_eq_compl_cusps :
    Set.range (rationalOpenImmersion h₂) = (cusps N)ᶜ := by
  rw [rationalOpenImmersion_range]
  ext x
  simp [cusps, X0Model3.finiteChart]

/-- The compact model's j-projection restricts to the actual source invariant
on the pinned affine level scheme. -/
theorem rationalOpenImmersion_jProjection :
    rationalOpenImmersion h₂ ≫ X0Model2.jProjection N =
      X0Model2.jLinePoint (algebraMap ℚ (Y0RationalAlgebra h₂)) (Y0RationalJ h₂) := by
  let hW := NormalModel.isAffineOpen_chart 0
  let hV := finiteChart_affine N
  let j := X0Model2.jProjection N
  let heq := (rationalChartSections h₂).property
  unfold rationalOpenImmersion X0Model2.jLinePoint
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec j hW hV le_rfl,
    Scheme.Hom.appLE_eq_app, ← Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  obtain ⟨f, rfl⟩ := (ProjectiveLine.polyEquivChart ℚ 0).surjective c
  change (rationalChartSections h₂).val (j.app finiteJChart
      (ProjectiveLine.polyEquivChart ℚ 0 f)) =
    (Y0RationalJMap h₂) ((ProjectiveLine.polyEquivChart ℚ 0).symm
      (ProjectiveLine.polyEquivChart ℚ 0 f))
  rw [RingEquiv.symm_apply_apply]
  exact heq f

#print axioms rationalAlgebra_isDomain
#print axioms rationalAlgebra_isIntegrallyClosed
#print axioms genericJ_isFractionRing
#print axioms finiteJChart_algebraMap
#print axioms rationalChartSections
#print axioms rationalOpenImmersion
#print axioms rationalOpenImmersion_isOpen
#print axioms cusps
#print axioms rationalOpenImmersion_range
#print axioms rationalOpenImmersion_range_eq_compl_cusps
#print axioms rationalOpenImmersion_jProjection

end WeierstrassCurve.ModelLevels.ModelGeneric2
