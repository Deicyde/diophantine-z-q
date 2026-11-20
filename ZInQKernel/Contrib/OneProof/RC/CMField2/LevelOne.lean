import ZInQKernel.Contrib.OneProof.RC.CMField2.Descent

/-! At level one the finite chart is already the affine j-line.
On-the-spot comparison (c), for tex 2915–2916. -/

noncomputable section

open AlgebraicGeometry CategoryTheory ModularCurve NumberField
  TauCeti.ClassFieldTheory TauCeti.GlobalNumberFields
open ZInQ.Contrib.CloudW07JacobiansCurves
open ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Manuscript.RC.PreparedParam

namespace ZInQ.Manuscript.RC.CMField2

attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

private abbrev W := NormalModel.chart 0

private theorem jPull_one_surjective :
    Function.Surjective ((X0Model2.jProjection 1).app W).hom := by
  let F := modularFunctionField 1
  let S := Γ(NormalModel.P, W)
  let T := Γ(Spec (.of F), NormalModel.f F ⁻¹ᵁ W)
  let K := NormalModel.P.functionField
  let : IsFractionRing S K := functionField_isFractionRing_of_isAffineOpen _ _
    (NormalModel.isAffineOpen_chart 0)
  have hF : modularFunctionField 1 = IntermediateField.adjoin ℚ {jq} := by
    change IntermediateField.adjoin ℚ {jq, jqN 1} = IntermediateField.adjoin ℚ {jq}
    rw [jqN_one, Set.pair_eq_singleton]
  have hφ : Function.Surjective (NormalModel.φ F) := by
    change Function.Surjective ((algebraMap (RatFunc ℚ) F) ∘ NormalModel.ratFuncEquiv.symm)
    apply Function.Surjective.comp _ NormalModel.ratFuncEquiv.symm.surjective
    change Function.Surjective ((Subfield.inclusion (show
      (IntermediateField.adjoin ℚ {jq}).toSubfield ≤ F.toSubfield from adjoin_jq_le 1)) ∘
      X0Model.jCoordinate)
    apply Function.Surjective.comp _ X0Model.jCoordinate.surjective
    intro x
    exact ⟨⟨x.val, hF ▸ x.property⟩, rfl⟩
  let : Algebra S F := NormalModel.algSecF F W
  let : Algebra K F := (NormalModel.φ F).toAlgebra
  let : IsScalarTower S K F := NormalModel.isScalarTower_secF F W
  let e : K ≃ₐ[S] F := AlgEquiv.ofBijective (IsScalarTower.toAlgHom S K F)
    ⟨(NormalModel.φ F).injective, hφ⟩
  let : IsFractionRing S F := IsFractionRing.of_algEquiv e
  let : Algebra S T := ((NormalModel.f F).app W).hom.toAlgebra
  let : IsFractionRing S T := IsFractionRing.of_algEquiv (NormalModel.εAlg F W).symm
  rw [show (X0Model2.jProjection 1).app W = (NormalModel.f F).fromNormalization.app W from rfl,
    (NormalModel.f F).fromNormalization_app (NormalModel.isAffineOpen_chart 0)]
  apply Function.Surjective.comp ((NormalModel.f F).normalizationObjIso
    (NormalModel.isAffineOpen_chart 0)).commRingCatIsoToRingEquiv.symm.surjective
  intro x
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral x.property
  exact ⟨y, Subtype.ext hy⟩

private theorem finiteEval_jPull (N : ℕ) [NeZero N] (τ : UpperHalfPlane) :
    (X0Branch.finitePointEval N τ).comp ((X0Model2.jProjection N).app W).hom =
      (Polynomial.eval₂RingHom (Rat.castHom ℂ) (X0Model.analyticJ τ)).comp
        (ProjectiveLine.polyEquivChart ℚ 0).symm.toRingHom := by
  let U := X0Branch.finiteChart N
  let hW := NormalModel.isAffineOpen_chart 0
  let hU := hW.preimage (X0Model2.jProjection N)
  let π := X0Model2.jProjection N
  let e := X0Branch.finitePointEval N τ
  have he : Spec.map (CommRingCat.ofHom e) ≫ hU.fromSpec = X0Model.complexPoint N τ :=
    affineEval_factor _ hU (chart_mem N τ)
  have hp : Spec.map (π.app W) ≫ hW.fromSpec = hU.fromSpec ≫ π := by
    rw [Scheme.Hom.app_eq_appLE π]
    exact IsAffineOpen.SpecMap_appLE_fromSpec π hW hU (le_rfl : U ≤ π ⁻¹ᵁ W)
  have h := X0Model2.complexPoint_jProjection N τ
  rw [← he, Category.assoc, ← hp, ← Category.assoc, ← Spec.map_comp, X0Model2.jLinePoint] at h
  exact congrArg CommRingCat.Hom.hom
    (Spec.map_injective ((cancel_mono hW.fromSpec).mp h))

private theorem finiteEval_jPull_mem_range (N : ℕ) [NeZero N] (τ : UpperHalfPlane)
    {F : Type} [Field F] [Algebra ℚ F] (ι : F →ₐ[ℚ] ℂ)
    (h : X0Model.analyticJ τ ∈ Set.range ι) (s : Γ(NormalModel.P, W)) :
    X0Branch.finitePointEval N τ ((X0Model2.jProjection N).app W s) ∈ Set.range ι := by
  let : CharZero F := charZero_of_injective_ringHom (algebraMap ℚ F).injective
  obtain ⟨x, hx⟩ := h
  let p := (ProjectiveLine.polyEquivChart ℚ 0).symm s
  refine ⟨p.eval₂ (Rat.castHom F) x, ?_⟩
  have he := DFunLike.congr_fun (finiteEval_jPull N τ) s
  change X0Branch.finitePointEval N τ _ =
    p.eval₂ (Rat.castHom ℂ) (X0Model.analyticJ τ) at he
  change ι.toRingHom (p.eval₂ (Rat.castHom F) x) = _
  change ι.toRingHom x = _ at hx
  rw [he, Polynomial.hom_eval₂, hx,
    show ι.toRingHom.comp (Rat.castHom F) = Rat.castHom ℂ from Subsingleton.elim _ _]

/-- At each level it suffices to test a fixed finite family of normalization
sections, provided that the first j-coordinate already lies in the image field. -/
theorem finiteChart_finiteTest (N : ℕ) [NeZero N] :
    ∃ s : Finset Γ(X0Model.curve N, X0Branch.finiteChart N),
      ∀ (τ : UpperHalfPlane) (F : Type) [Field F] [Algebra ℚ F] (ι : F →ₐ[ℚ] ℂ),
        X0Model.analyticJ τ ∈ Set.range ι →
        (∀ r ∈ s, X0Branch.finitePointEval N τ r ∈ Set.range ι) →
        ∀ r, X0Branch.finitePointEval N τ r ∈ Set.range ι := by
  classical
  let A := Γ(NormalModel.P, W)
  let S := Γ(X0Model.curve N, X0Branch.finiteChart N)
  let j := ((X0Model2.jProjection N).app W).hom
  let : Algebra A S := j.toAlgebra
  have hj : (algebraMap A S).Finite := NormalModel.finite_app (modularFunctionField N) W
    (NormalModel.isAffineOpen_chart 0)
  let : Module.Finite A S := RingHom.finite_algebraMap.mp hj
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := S)
  refine ⟨s, fun τ F _ _ ι h hre r => ?_⟩
  let e := X0Branch.finitePointEval N τ
  let B : Submodule A S :=
    { carrier := {r | e r ∈ ι.toRingHom.range}
      zero_mem' := by
        change e 0 ∈ ι.toRingHom.range
        rw [map_zero]
        exact ι.toRingHom.range.zero_mem
      add_mem' := by
        intro x y hx hy
        change e (x + y) ∈ ι.toRingHom.range
        rw [map_add]
        exact ι.toRingHom.range.add_mem hx hy
      smul_mem' := by
        intro a x hx
        change e (a • x) ∈ ι.toRingHom.range
        rw [Algebra.smul_def, map_mul]
        exact ι.toRingHom.range.mul_mem (finiteEval_jPull_mem_range N τ ι h a) hx }
  have hle : Submodule.span A (s : Set S) ≤ B := Submodule.span_le.mpr hre
  rw [hs] at hle
  exact hle (Submodule.mem_top : r ∈ (⊤ : Submodule A S))

/-- At level one, every finite-chart value lies in the image field if the first
j-coordinate does. -/
theorem finitePointEval_one_mem_range (τ : UpperHalfPlane)
    {F : Type} [Field F] [Algebra ℚ F] (ι : F →ₐ[ℚ] ℂ)
    (h : X0Model.analyticJ τ ∈ Set.range ι) :
    ∀ r, X0Branch.finitePointEval 1 τ r ∈ Set.range ι := by
  intro r
  obtain ⟨s, rfl⟩ := jPull_one_surjective r
  exact finiteEval_jPull_mem_range 1 τ ι h s

/-- Descent of a level-one point from the first j-coordinate. -/
theorem modelOne_fieldPoint_of_analyticJ (τ : UpperHalfPlane)
    {F : Type} [Field F] [Algebra ℚ F] (ι : F →ₐ[ℚ] ℂ)
    (h : X0Model.analyticJ τ ∈ Set.range ι) :
    ∃ x : FieldPoint X0Model2.modelOne.overQ F, x.map ι = X0Model2.modelOne.complexPoint τ :=
  fieldPoint_of_finitePointEval_range 1 τ ι (finitePointEval_one_mem_range τ ι h)


end ZInQ.Manuscript.RC.CMField2
