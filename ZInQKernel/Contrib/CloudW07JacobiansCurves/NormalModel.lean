import ZInQKernel.Contrib.CurvesG.CurveSplit
import ZInQKernel.Contrib.Dim.IntegralHom
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveLine.BasicOpens
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.ProjectiveLine.Geometry
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# cloud-w07: frontier row H-80, `ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ`, proved

The fixed statement (`ZInQKernel/Contrib/CurvesG/CurveSplit.lean`, fork `main` at `cba8157f`):
every finite extension `F` of `ℚ(T)` is the function field of a proper integral scheme `X` over
`ℚ`, normal (all stalks integrally closed) and of dimension `1`.

The proof is the textbook one (Stacks, *Algebraic Curves*, section on curves and function
fields; Hartshorne I.6, II.6.7): `X` is the relative normalization of `ℙ¹_ℚ` in `Spec F`, for the
morphism `f : Spec F ⟶ ℙ¹_ℚ` through the generic point given by `K(ℙ¹) ≅ ℚ(T) ⊆ F`.

* `ℙ¹_ℚ` is `AlgebraicGeometry.projectiveLine ℚ = Proj ℚ[X₀, X₁]` of the vendored
  `frenzymath/Jacobian-Challenge` library (properness, integrality, the two charts with
  `Γ ≅ ℚ[X]`); the relative normalization `f.normalization` with its integral map
  `ν = f.fromNormalization` and the affine-local description of its sections by integral
  closures (`normalizationObjIso`, `fromNormalization_app`) is Mathlib's (Stacks 035H).
* Finiteness of `ν` over the charts: the integral closure of `ℚ[X]` in the finite (separable,
  characteristic `0`) extension `F` of `ℚ(X)` is a finite `ℚ[X]`-module
  (`IsIntegralClosure.finite`). So `ν` is finite, hence proper, and `X → ℙ¹ → Spec ℚ` is proper.
* `X` is integral (Mathlib: the normalization of an integral scheme), normal (its sections over
  the preimage of a chart are an integral closure in a field, hence integrally closed, and its
  stalks are localizations of those), of dimension `dim ℙ¹ = 1` (`ν` is integral and surjective;
  `ZInQ.Contrib.Dim`), and its function field is the fraction field `F` of an integral closure
  (`integralClosure.isFractionRing_of_finite_extension`).

No `sorry`, no `axiom`; the statement is the fixed `def`, unchanged.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace ZInQ.Contrib.CloudW07JacobiansCurves

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace IsLocalRing

namespace NormalModel

/-! ## The projective line over `ℚ` -/

/-- `ℙ¹_ℚ = Proj ℚ[X₀, X₁]`. -/
abbrev P : Scheme.{0} := projectiveLine ℚ

/-- The standard chart `D₊(Xᵢ)` of `ℙ¹_ℚ`. -/
abbrev chart (i : Fin 2) : P.Opens := ProjectiveLine.chart ℚ i

lemma isAffineOpen_chart (i : Fin 2) : IsAffineOpen (chart i) :=
  ProjectiveLine.isAffineOpen_chart ℚ i

instance chart_nonempty (i : Fin 2) : Nonempty (chart i) := by
  have : Nontrivial Γ(P, chart i) :=
    (ProjectiveLine.polyEquivChart ℚ i).symm.toEquiv.nontrivial
  obtain ⟨p⟩ := (inferInstance : Nonempty (PrimeSpectrum Γ(P, chart i)))
  exact ⟨(isAffineOpen_chart i).isoSpec.inv p⟩

instance chart_isIntegrallyClosed (i : Fin 2) : IsIntegrallyClosed Γ(P, chart i) :=
  IsIntegrallyClosed.of_equiv (ProjectiveLine.polyEquivChart ℚ i)

instance : IsLocallyNoetherian P :=
  LocallyOfFiniteType.isLocallyNoetherian (projectiveLineToSpec ℚ)

lemma genericPoint_mem (W : P.Opens) [h : Nonempty W] : genericPoint P ∈ W :=
  ((genericPoint_spec P).mem_open_set_iff W.isOpen).mpr (by simpa using h)

lemma exists_chart (y : P) : ∃ i, y ∈ chart i := by
  have : y ∈ (⨆ i, chart i : P.Opens) := by
    rw [ProjectiveLine.iSup_chart_eq_top]
    trivial
  exact Opens.mem_iSup.mp this

/-- `ℚ(T) ≃ K(ℙ¹_ℚ)`, through the chart `D₊(X₀)` with `Γ ≅ ℚ[X]`. -/
def ratFuncEquiv : LeafModCurves.Qj ≃+* P.functionField :=
  haveI : IsFractionRing Γ(P, chart 0) P.functionField :=
    functionField_isFractionRing_of_isAffineOpen P (chart 0) (isAffineOpen_chart 0)
  IsFractionRing.ringEquivOfRingEquiv (ProjectiveLine.polyEquivChart ℚ 0)

/-- `dim ℙ¹_ℚ = 1`: both charts are `Spec ℚ[X]`. -/
lemma topologicalKrullDim_P : topologicalKrullDim P = 1 := by
  have hcov : ∀ x : P, ∃ i : Fin 2, x ∈ Set.range (fun y : ((chart i : P.Opens) : Set P) => (y : P)) := by
    intro x
    obtain ⟨i, hi⟩ := exists_chart x
    exact ⟨i, ⟨x, hi⟩, rfl⟩
  rw [ZInQ.Contrib.Dim.topologicalKrullDim_eq_iSup_of_isOpenEmbedding
    (Y := fun i : Fin 2 => ((chart i : P.Opens) : Set P)) (fun i y => (y : P))
    (fun i => (chart i).isOpen.isOpenEmbedding_subtypeVal) hcov]
  have h : ∀ i : Fin 2, topologicalKrullDim ((chart i : P.Opens) : Set P) = 1 := by
    intro i
    rw [show topologicalKrullDim ((chart i : P.Opens) : Set P) =
        topologicalKrullDim (chart i).toScheme from rfl,
      ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_iso (isAffineOpen_chart i).isoSpec,
      ZInQ.Contrib.Dim.topologicalKrullDim_spec,
      ← ringKrullDim_eq_of_ringEquiv (ProjectiveLine.polyEquivChart ℚ i),
      Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add]
  simp only [h, ciSup_const]

/-! ## The morphism `Spec F ⟶ ℙ¹_ℚ` through the generic point -/

section Field

variable (F : Type) [Field F] [Algebra LeafModCurves.Qj F]

/-- `K(ℙ¹_ℚ) ≅ ℚ(T) ⊆ F`. -/
def φ : P.functionField →+* F :=
  (algebraMap LeafModCurves.Qj F).comp ratFuncEquiv.symm.toRingHom

/-- `F` is finite over `K(ℙ¹_ℚ)` through `φ`. -/
lemma finite_φ [FiniteDimensional LeafModCurves.Qj F] : (φ F).Finite := by
  have h1 : (algebraMap LeafModCurves.Qj F).Finite := RingHom.finite_algebraMap.mpr inferInstance
  have h2 : (ratFuncEquiv.symm.toRingHom : P.functionField →+* LeafModCurves.Qj).Finite :=
    RingHom.Finite.of_surjective _ ratFuncEquiv.symm.surjective
  exact h1.comp h2

/-- `f : Spec F ⟶ ℙ¹_ℚ`, through the generic point. -/
def f : Spec (CommRingCat.of F) ⟶ P :=
  Spec.map (CommRingCat.ofHom (φ F)) ≫ P.fromSpecStalk (genericPoint P)

lemma f_closedPoint : f F (closedPoint (CommRingCat.of F)) = genericPoint P := by
  rw [f, Scheme.Hom.comp_apply, Spec_closedPoint]
  exact Scheme.fromSpecStalk_closedPoint

lemma closedPoint_mem (W : P.Opens) [Nonempty W] : f F (closedPoint (CommRingCat.of F)) ∈ W := by
  rw [f_closedPoint]
  exact genericPoint_mem W

instance : QuasiCompact (f F) := by
  have : QuasiCompact (f F ≫ projectiveLineToSpec ℚ) := inferInstance
  exact QuasiCompact.of_comp (f F) (projectiveLineToSpec ℚ)

instance : QuasiSeparated (f F) := inferInstance

/-- `Γ(Spec F, f⁻¹ W) ≅ F` for `W` nonempty (then `f⁻¹ W = ⊤`). -/
def εIso (W : P.Opens) [Nonempty W] :
    Γ(Spec (CommRingCat.of F), f F ⁻¹ᵁ W) ≅ CommRingCat.of F :=
  (Spec (CommRingCat.of F)).presheaf.mapIso
    (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem (f F) (closedPoint_mem F W)).symm).op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of F)

/-- The key compatibility: on sections, `f` is `φ` after the germ at the generic point. -/
lemma app_εIso (W : P.Opens) [Nonempty W] :
    (f F).app W ≫ (εIso F W).hom = P.germToFunctionField W ≫ CommRingCat.ofHom (φ F) := by
  rw [εIso, ← Scheme.germ_stalkClosedPointTo (f F) W (closedPoint_mem F W)]
  simp only [f]
  rw [Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk]

lemma εIso_app_apply (W : P.Opens) [Nonempty W] (a : Γ(P, W)) :
    (εIso F W).hom.hom (((f F).app W).hom a) = φ F ((P.germToFunctionField W).hom a) := by
  have h := congrArg (fun g => g a) (congrArg CommRingCat.Hom.hom (app_εIso F W))
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] using h

/-! ## The relative normalization and its sections -/

/-- The relative normalization of `ℙ¹_ℚ` in `Spec F`: the normal model. -/
abbrev Xn : Scheme.{0} := (f F).normalization

/-- Its integral structure morphism to `ℙ¹_ℚ`. -/
abbrev ν : Xn F ⟶ P := (f F).fromNormalization

section Sections

variable (W : P.Opens) [Nonempty W]

/-- `F` as a `Γ(ℙ¹, W)`-algebra, through `ε ∘ f.app W`. -/
abbrev algSecF : Algebra Γ(P, W) F :=
  ((εIso F W).hom.hom.comp ((f F).app W).hom).toAlgebra

/-- `Γ(Spec F, f⁻¹ W) ≅ F` as `Γ(ℙ¹, W)`-algebras. -/
def εAlg :
    letI := ((f F).app W).hom.toAlgebra
    letI := algSecF F W
    Γ(Spec (CommRingCat.of F), f F ⁻¹ᵁ W) ≃ₐ[Γ(P, W)] F :=
  letI := ((f F).app W).hom.toAlgebra
  letI := algSecF F W
  AlgEquiv.ofRingEquiv (f := (εIso F W).commRingCatIsoToRingEquiv) (fun _ => rfl)

lemma isScalarTower_secF :
    let := algSecF F W
    let := (φ F).toAlgebra
    IsScalarTower Γ(P, W) P.functionField F := by
  let := algSecF F W
  let := (φ F).toAlgebra
  exact IsScalarTower.of_algebraMap_eq (fun a => εIso_app_apply F W a)

/-- **Finiteness of the integral closure** of `Γ(ℙ¹, W)` in `F`. -/
lemma finite_integralClosure_F [FiniteDimensional LeafModCurves.Qj F] [IsIntegrallyClosed Γ(P, W)]
    (hW : IsAffineOpen W) :
    let := algSecF F W
    Module.Finite Γ(P, W) (integralClosure Γ(P, W) F) := by
  let := algSecF F W
  let := (φ F).toAlgebra
  have := isScalarTower_secF F W
  have : IsFractionRing Γ(P, W) P.functionField :=
    functionField_isFractionRing_of_isAffineOpen P W hW
  have : IsNoetherianRing Γ(P, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have : FiniteDimensional P.functionField F := finite_φ F
  have : CharZero P.functionField :=
    charZero_of_injective_ringHom (ratFuncEquiv.toRingHom.injective)
  have : Algebra.IsSeparable P.functionField F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact IsIntegralClosure.finite Γ(P, W) P.functionField F (integralClosure Γ(P, W) F)

/-- The integral closure of `Γ(ℙ¹, W)` in `Γ(Spec F, f⁻¹ W)` is a finite module. -/
lemma finite_integralClosure [FiniteDimensional LeafModCurves.Qj F] [IsIntegrallyClosed Γ(P, W)]
    (hW : IsAffineOpen W) :
    let := ((f F).app W).hom.toAlgebra
    Module.Finite Γ(P, W) (integralClosure Γ(P, W) Γ(Spec (CommRingCat.of F), f F ⁻¹ᵁ W)) := by
  let := ((f F).app W).hom.toAlgebra
  let := algSecF F W
  have := finite_integralClosure_F F W hW
  exact Module.Finite.equiv (εAlg F W).mapIntegralClosure.symm.toLinearEquiv

/-- `ν` is finite over `W`. -/
lemma finite_app [FiniteDimensional LeafModCurves.Qj F] [IsIntegrallyClosed Γ(P, W)]
    (hW : IsAffineOpen W) : ((ν F).app W).hom.Finite := by
  rw [Scheme.Hom.fromNormalization_app (f F) hW, CommRingCat.hom_comp, CommRingCat.hom_ofHom]
  let := ((f F).app W).hom.toAlgebra
  have h1 : (algebraMap Γ(P, W)
      (integralClosure Γ(P, W) Γ(Spec (CommRingCat.of F), f F ⁻¹ᵁ W))).Finite :=
    RingHom.finite_algebraMap.mpr (finite_integralClosure F W hW)
  have h2 : ((f F).normalizationObjIso hW).inv.hom.Finite :=
    RingHom.Finite.of_surjective _
      ((f F).normalizationObjIso hW).commRingCatIsoToRingEquiv.symm.surjective
  exact h2.comp h1

/-- The integral closure of `Γ(ℙ¹, W)` in `F` is integrally closed. -/
lemma isIntegrallyClosed_integralClosure_F :
    let := algSecF F W
    IsIntegrallyClosed (integralClosure Γ(P, W) F) := by
  let := algSecF F W
  exact IsIntegrallyClosed.of_isIntegrallyClosedIn (integralClosure Γ(P, W) F) F

/-- The sections of the normalization over `ν⁻¹ W` are integrally closed. -/
lemma isIntegrallyClosed_sections (hW : IsAffineOpen W) :
    IsIntegrallyClosed Γ(Xn F, ν F ⁻¹ᵁ W) := by
  let := ((f F).app W).hom.toAlgebra
  let := algSecF F W
  have := isIntegrallyClosed_integralClosure_F F W
  have : IsIntegrallyClosed
      (integralClosure Γ(P, W) Γ(Spec (CommRingCat.of F), f F ⁻¹ᵁ W)) :=
    IsIntegrallyClosed.of_equiv (εAlg F W).mapIntegralClosure.symm.toRingEquiv
  exact IsIntegrallyClosed.of_equiv ((f F).normalizationObjIso hW).commRingCatIsoToRingEquiv.symm

end Sections

/-! ## The normal model -/

/-- `ν` is finite. -/
instance isFinite_ν [FiniteDimensional LeafModCurves.Qj F] : IsFinite (ν F) := by
  rw [HasAffineProperty.iff_of_iSup_eq_top (P := @IsFinite)
    (fun i : Fin 2 => (⟨chart i, isAffineOpen_chart i⟩ : P.affineOpens))
    (ProjectiveLine.iSup_chart_eq_top ℚ)]
  intro i
  refine ⟨(isAffineOpen_chart i).preimage (ν F), ?_⟩
  have hW : (chart i).ι ''ᵁ ⊤ = chart i := Scheme.Opens.ι_image_top _
  have : Nonempty ((chart i).ι ''ᵁ ⊤) := by rw [hW]; infer_instance
  have : IsIntegrallyClosed Γ(P, (chart i).ι ''ᵁ ⊤) := by rw [hW]; infer_instance
  have hA : IsAffineOpen ((chart i).ι ''ᵁ ⊤) := by rw [hW]; exact isAffineOpen_chart i
  rw [morphismRestrict_appTop, CommRingCat.hom_comp]
  refine RingHom.Finite.comp ?_ (finite_app F _ hA)
  exact RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2

instance [FiniteDimensional LeafModCurves.Qj F] : IsProper (ν F ≫ projectiveLineToSpec ℚ) :=
  inferInstance

/-- `ν` is surjective: it is closed, and its image contains the generic point. -/
instance surjective_ν : Surjective (ν F) := by
  have hclosed : IsClosed (Set.range (ν F)) := (ν F).isClosedMap.isClosed_range
  have hmem : genericPoint P ∈ Set.range (ν F) :=
    ⟨(f F).toNormalization (closedPoint (CommRingCat.of F)), by
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.toNormalization_fromNormalization, f_closedPoint]⟩
  have huniv : Set.range (ν F) = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    rw [← genericPoint_closure P]
    exact hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)
  exact ⟨Set.range_eq_univ.mp huniv⟩

lemma topologicalKrullDim_Xn : topologicalKrullDim (Xn F) = 1 := by
  rw [ZInQ.Contrib.Dim.topologicalKrullDim_eq_of_isIntegralHom_of_surjective (ν F),
    topologicalKrullDim_P]

/-- The normal model is normal: every stalk is integrally closed. -/
lemma isNormalScheme_Xn : ZInQ.Contrib.CurvesG.IsNormalScheme (Xn F) := by
  intro x
  obtain ⟨i, hi⟩ := exists_chart ((ν F) x)
  have hV : IsAffineOpen (ν F ⁻¹ᵁ chart i) := (isAffineOpen_chart i).preimage (ν F)
  have hx : x ∈ ν F ⁻¹ᵁ chart i := hi
  have : Nonempty (ν F ⁻¹ᵁ chart i) := ⟨⟨x, hx⟩⟩
  have := isIntegrallyClosed_sections F (chart i) (isAffineOpen_chart i)
  let := TopCat.Presheaf.algebra_section_stalk (Xn F).presheaf (⟨x, hx⟩ : ν F ⁻¹ᵁ chart i)
  have := hV.isLocalization_stalk ⟨x, hx⟩
  exact isIntegrallyClosed_of_isLocalization ((Xn F).presheaf.stalk x)
    (hV.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _)

/-- The function field of the normal model is `F`. -/
def functionFieldEquiv [FiniteDimensional LeafModCurves.Qj F] : (Xn F).functionField ≃+* F := by
  have hW := isAffineOpen_chart 0
  have hV : IsAffineOpen (ν F ⁻¹ᵁ chart 0) := hW.preimage (ν F)
  haveI : Nonempty (ν F ⁻¹ᵁ chart 0) := by
    obtain ⟨y⟩ := (inferInstance : Nonempty (chart 0))
    obtain ⟨x, hx⟩ := (ν F).surjective y.1
    exact ⟨⟨x, by rw [Scheme.Hom.mem_preimage, hx]; exact y.2⟩⟩
  haveI : IsFractionRing Γ(Xn F, ν F ⁻¹ᵁ chart 0) (Xn F).functionField :=
    functionField_isFractionRing_of_isAffineOpen _ _ hV
  letI := ((f F).app (chart 0)).hom.toAlgebra
  letI := algSecF F (chart 0)
  letI := (φ F).toAlgebra
  haveI := isScalarTower_secF F (chart 0)
  haveI : FiniteDimensional P.functionField F := finite_φ F
  haveI : IsFractionRing Γ(P, chart 0) P.functionField :=
    functionField_isFractionRing_of_isAffineOpen P (chart 0) hW
  haveI : IsFractionRing (integralClosure Γ(P, chart 0) F) F :=
    integralClosure.isFractionRing_of_finite_extension P.functionField F
  exact IsFractionRing.ringEquivOfRingEquiv
    (((f F).normalizationObjIso hW).commRingCatIsoToRingEquiv.trans
      (εAlg F (chart 0)).mapIntegralClosure.toRingEquiv)

end Field

end NormalModel

open NormalModel in
/-- **Frontier row H-80, proved:** `ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ`. -/
theorem NormalModelOfFunctionFieldQ_proof : ZInQ.Contrib.CurvesG.NormalModelOfFunctionFieldQ := by
  intro F _ _ _
  refine ⟨Over.mk (ν F ≫ projectiveLineToSpec ℚ), ?_, ?_⟩
  · show IsProper (ν F ≫ projectiveLineToSpec ℚ)
    infer_instance
  · refine ⟨(inferInstance : IsIntegral (Xn F)), isNormalScheme_Xn F, topologicalKrullDim_Xn F,
      ⟨functionFieldEquiv F⟩⟩

end ZInQ.Contrib.CloudW07JacobiansCurves
