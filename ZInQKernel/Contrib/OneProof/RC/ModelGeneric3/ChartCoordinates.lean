import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.QuotientRegularity

/-! # The second coordinate on the fixed normalization -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric3

open AlgebraicGeometry CategoryTheory Filter ModularCurve
open ModelGeneric ModelGeneric2
open ZInQ.Manuscript.RC
open ZInQ.Contrib.CloudW07JacobiansCurves

open private genericJ_isFractionRing rationalAlgebra_isDomain
  rationalAlgebra_isIntegrallyClosed finiteJChart_algebraMap from
  ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.AffineComparison
open private affineEval_factor chart_mem_finiteChart finiteChart_affine from
  ZInQKernel.Contrib.OneProof.RC.X0Model3.AffineEval
open private jLinePoint_comp jLinePoint_injective from
  ZInQKernel.Contrib.OneProof.RC.X0Model2.Projection

attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 80000
set_option linter.style.haveILetI false

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

/-- The regular quotient coordinate on the named finite chart, obtained from the
actual iterated Vélu coordinate using the integral-closure isomorphism. -/
noncomputable def branchQuotientCoordinate :
    Γ(X0Model.curve N, X0Model3.finiteChart N) :=
  (rationalChartSections h₂).val.symm (rationalQuotientCoordinate h₂).val

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
private theorem normalization_section_field
    (s : Γ(X0Model.curve N, X0Model3.finiteChart N)) :
    X0Model.functionField N ((X0Model.curve N).germToFunctionField (X0Model3.finiteChart N) s) =
      (NormalModel.εAlg (modularFunctionField N) (NormalModel.chart 0))
        ((NormalModel.f (modularFunctionField N)).normalizationObjIso
          (NormalModel.isAffineOpen_chart 0) |>.hom s).val := by
  let F := modularFunctionField N
  let U := NormalModel.chart 0
  let S := Γ(X0Model.curve N, X0Model3.finiteChart N)
  let C := Γ(NormalModel.P, U)
  let hW := NormalModel.isAffineOpen_chart 0
  let hV := hW.preimage (NormalModel.ν F)
  let : Nonempty (X0Model3.finiteChart N) := ⟨⟨_, chart_mem_finiteChart N default⟩⟩
  let : IsFractionRing S (X0Model.curve N).functionField :=
    functionField_isFractionRing_of_isAffineOpen _ _ hV
  let := ((NormalModel.f F).app U).hom.toAlgebra
  let := NormalModel.algSecF F U
  let := (NormalModel.φ F).toAlgebra
  let : IsScalarTower C NormalModel.P.functionField F := NormalModel.isScalarTower_secF F U
  let : FiniteDimensional NormalModel.P.functionField F := NormalModel.finite_φ F
  let : IsFractionRing C NormalModel.P.functionField :=
    functionField_isFractionRing_of_isAffineOpen _ _ hW
  let : IsFractionRing (integralClosure C F) F :=
    integralClosure.isFractionRing_of_finite_extension NormalModel.P.functionField F
  change IsFractionRing.ringEquivOfRingEquiv
      (((NormalModel.f F).normalizationObjIso hW).commRingCatIsoToRingEquiv.trans
        (NormalModel.εAlg F U).mapIntegralClosure.toRingEquiv)
      (algebraMap S (X0Model.curve N).functionField s) = _
  rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
  rfl

set_option maxHeartbeats 4000000 in
/-- The isomorphism of the integral closures uses the prescribed field map. -/
private theorem section_fieldComparison (s : Γ(X0Model.curve N, X0Model3.finiteChart N)) :
    X0Model.functionField N ((X0Model.curve N).germToFunctionField (X0Model3.finiteChart N) s) =
      genericModularFieldEquiv h₂ (Classical.choice (nonempty_modularPolynomialData N))
        (Y0RationalGenericJInclusion h₂ ((rationalChartSections h₂).val s)) := by
  let P := Polynomial ℚ
  let B : Type := Y0RationalAlgebra h₂
  let E := Y0RationalGenericJ h₂
  let F := modularFunctionField N
  let U := NormalModel.chart 0
  let C := Γ(NormalModel.P, U)
  let p := ProjectiveLine.polyEquivChart ℚ 0
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  letI : Field E := genericJField h₂
  letI : IsDomain B := rationalAlgebra_isDomain h₂
  letI : IsIntegrallyClosed B := rationalAlgebra_isIntegrallyClosed h₂
  letI : IsFractionRing B E := genericJ_isFractionRing h₂
  let e := genericModularFieldEquiv h₂ (Classical.choice (nonempty_modularPolynomialData N))
  letI : Algebra B F := (e.toRingHom.comp (algebraMap B E)).toAlgebra
  let e' : E ≃ₐ[B] F := AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun _ => rfl
  letI : IsFractionRing B F := IsFractionRing.of_algEquiv e'
  letI : Algebra C B := ((Y0RationalJMap h₂).toRingHom.comp p.symm.toRingHom).toAlgebra
  have hFinite : (Y0RationalJMap h₂).toRingHom.Finite :=
    RingHom.finite_algebraMap.mpr (Y0RationalJMap_finite h₂)
  letI : Module.Finite C B := RingHom.finite_algebraMap.mp
    (hFinite.comp (RingHom.Finite.of_surjective _ p.symm.surjective))
  letI := NormalModel.algSecF F U
  letI : IsScalarTower C B F := IsScalarTower.of_algebraMap_eq fun c => by
    obtain ⟨f, rfl⟩ := p.surjective c
    rw [finiteJChart_algebraMap (N := N), ← e.commutes]
    change _ = e (algebraMap B E (Y0RationalJMap h₂ (p.symm (p f))))
    rw [RingEquiv.symm_apply_apply]
    congr 1
    exact (Algebra.TensorProduct.includeRight (R := P)
      (A := LeafModCurves.Qj) (B := B)).commutes f |>.symm
  letI : IsIntegralClosure B B F :=
    (isIntegrallyClosed_iff_isIntegralClosure F).mp (rationalAlgebra_isIntegrallyClosed h₂)
  letI : IsIntegralClosure B C F := IsIntegralClosure.of_isIntegrallyClosedIn
  letI := ((NormalModel.f F).app U).hom.toAlgebra
  let normIso := (NormalModel.f F).normalizationObjIso (NormalModel.isAffineOpen_chart 0)
  let sectionIso := normIso.commRingCatIsoToRingEquiv.trans
    (NormalModel.εAlg F U).mapIntegralClosure.toRingEquiv
  let closureIso := IsIntegralClosure.equiv C B F (integralClosure C F)
  rw [normalization_section_field]
  change (sectionIso s : F) = algebraMap B F (closureIso.symm (sectionIso s))
  have h := IsIntegralClosure.algebraMap_equiv C B F (integralClosure C F)
    (closureIso.symm (sectionIso s))
  change (closureIso (closureIso.symm (sectionIso s)) : F) = _ at h
  rw [closureIso.apply_symm_apply] at h
  exact h

/-- The field value of the regular second coordinate is the prescribed Laurent
generator of the normalization. -/
theorem branchQuotientCoordinate_field :
    X0Model.functionField N ((X0Model.curve N).germToFunctionField (X0Model3.finiteChart N)
      (branchQuotientCoordinate h₂)) = ⟨jqN N, jqN_mem N⟩ := by
  rw [section_fieldComparison h₂, branchQuotientCoordinate, RingEquiv.apply_symm_apply,
    (rationalQuotientCoordinate h₂).property, genericModularFieldEquiv_quotientJ]

/-- The second coordinate at every analytic branch is the value of j(Nτ),
including parameters where different branches have equal coordinate values. -/
theorem branchQuotientCoordinate_complexPoint (τ : UpperHalfPlane) :
    X0Model3.finitePointEval N τ (branchQuotientCoordinate h₂) = X0Model.analyticJN N τ := by
  let U := X0Model3.finiteChart N
  have hτ := chart_mem_finiteChart N τ
  letI : Nonempty U := ⟨⟨_, hτ⟩⟩
  obtain ⟨g, hg, he, hv⟩ := X0Model.sectionAnalyticAt N τ U
    (branchQuotientCoordinate h₂) hτ
  rw [branchQuotientCoordinate_field h₂, X0Model.fieldGerm_jN] at he
  change X0Model3.finitePointEval N τ (branchQuotientCoordinate h₂) = _
  refine hv.trans ?_
  have ha := X0Model.analyticOn_jN N τ τ.im_pos
  have h := tendsto_nhds_unique
    (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (ha.continuousAt.tendsto.mono_left nhdsWithin_le_nhds |>.congr'
      (Filter.Germ.coe_eq.mp he.symm))
  simpa only [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using h

/-- Evaluate the pinned rational algebra at the inverse image of the actual
analytic point of the normalization. -/
noncomputable def rationalPointAtParameter (τ : UpperHalfPlane) :
    Y0RationalAlgebra h₂ →ₐ[ℚ] ℂ :=
  ((X0Model3.finitePointEval N τ).comp (rationalChartSections h₂).val.symm.toRingHom).toRatAlgHom

/-- The inverse evaluation maps to the full point of the normalization. -/
theorem rationalPointAtParameter_openImmersion (τ : UpperHalfPlane) :
    Spec.map (CommRingCat.ofHom (rationalPointAtParameter h₂ τ).toRingHom) ≫
      rationalOpenImmersion h₂ = X0Model.complexPoint N τ := by
  rw [rationalOpenImmersion, ← Category.assoc, ← Spec.map_comp]
  have h : CommRingCat.ofHom (rationalChartSections h₂).val.toRingHom ≫
      CommRingCat.ofHom (rationalPointAtParameter h₂ τ).toRingHom =
      CommRingCat.ofHom (X0Model3.finitePointEval N τ) := by
    ext s
    change X0Model3.finitePointEval N τ
      ((rationalChartSections h₂).val.symm ((rationalChartSections h₂).val s)) =
      X0Model3.finitePointEval N τ s
    rw [RingEquiv.symm_apply_apply]
  rw [h]
  exact affineEval_factor _ (finiteChart_affine N) (chart_mem_finiteChart N τ)

/-- The first invariant of the pinned pair at the inverse evaluation is
the j-value of the analytic parameter. -/
theorem rationalPointAtParameter_pairJ (τ : UpperHalfPlane) :
    pairJ (rationalPoints h₂ (rationalPointAtParameter h₂ τ)) = X0Model.analyticJ τ := by
  let x := rationalPointAtParameter h₂ τ
  have h := congrArg (fun y => y ≫ X0Model2.jProjection N)
    (rationalPointAtParameter_openImmersion h₂ τ)
  rw [Category.assoc, rationalOpenImmersion_jProjection, jLinePoint_comp,
    X0Model2.complexPoint_jProjection] at h
  have hq : x.toRingHom.comp (algebraMap ℚ (Y0RationalAlgebra h₂)) = Rat.castHom ℂ :=
    Subsingleton.elim _ _
  change X0Model2.jLinePoint (x.toRingHom.comp _) (x (Y0RationalJ h₂)) = _ at h
  rw [hq] at h
  exact (rationalPoints_j h₂ x).trans (jLinePoint_injective h)

/-- At the same inverse evaluation the regular quotient coordinate equals
the second analytic coordinate of the full normalized point. -/
theorem rationalPointAtParameter_quotientCoordinate (τ : UpperHalfPlane) :
    rationalPointAtParameter h₂ τ (rationalQuotientCoordinate h₂).val =
      X0Model.analyticJN N τ :=
  branchQuotientCoordinate_complexPoint h₂ τ

#print axioms branchQuotientCoordinate
#print axioms normalization_section_field
#print axioms section_fieldComparison
#print axioms branchQuotientCoordinate_field
#print axioms branchQuotientCoordinate_complexPoint
#print axioms rationalPointAtParameter
#print axioms rationalPointAtParameter_openImmersion
#print axioms rationalPointAtParameter_pairJ
#print axioms rationalPointAtParameter_quotientCoordinate

end WeierstrassCurve.ModelLevels.ModelGeneric3
