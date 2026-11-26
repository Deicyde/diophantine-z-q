import ZInQKernel.Contrib.OneProof.NeronSchemeExtensionExists
import ZInQKernel.Contrib.OneProof.RC.GoodReduction.Integral
import ZInQKernel.Contrib.OneProof.RC.J0Cusps.ProjectiveGroupLaw
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric.ShortBaseChange

/-! Local existence for the fixed elliptic target, tex 8476–8479.
The local-ring and generic-fibre identifications are on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField PkgI3
open WeierstrassCurve.ModelTorsion WeierstrassCurve.ModelLevels.ModelGeneric

namespace ZInQ.Manuscript.RC.ModelNeron

open GoodReduction (generic)
open ZInQ.Contrib.NeronC
open scoped MonoidalCategory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

variable (ell : ℕ) [Fact ell.Prime]

private abbrev numberFieldPrime : Ideal (𝓞 ℚ) :=
  (integerPrimeIdeal ell).comap Rat.ringOfIntegersEquiv.toRingHom

private def numberFieldAlgebra : Algebra (𝓞 ℚ) (LocalIntegers ell) :=
  ((algebraMap ℤ (LocalIntegers ell)).comp Rat.ringOfIntegersEquiv.toRingHom).toAlgebra

private theorem numberFieldPrime_isMaximal : (numberFieldPrime ell).IsMaximal := by
  have hp : (integerPrimeIdeal ell).IsMaximal :=
    (Nat.prime_iff_prime_int.mp (Fact.out : ell.Prime)).isMaximal_span_singleton
  exact hp.comap_bijective _ Rat.ringOfIntegersEquiv.bijective

private theorem detector_isLocalization :
    letI := numberFieldAlgebra ell
    IsLocalization.AtPrime (LocalIntegers ell) (numberFieldPrime ell) := by
  let e := Rat.ringOfIntegersEquiv
  let p := integerPrimeIdeal ell
  have hv : p.primeCompl.map e.symm = (numberFieldPrime ell).primeCompl := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (e.symm y) ∉ p
      rw [e.apply_symm_apply]
      exact hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  have h := IsLocalization.isLocalization_of_base_ringEquiv p.primeCompl (LocalIntegers ell) e.symm
  rwa [hv] at h

private theorem detector_isScalarTower :
    letI := numberFieldAlgebra ell
    IsScalarTower (𝓞 ℚ) (LocalIntegers ell) ℚ := by
  letI := numberFieldAlgebra ell
  let p := integerPrimeIdeal ell
  haveI := IsLocalization.localization_isScalarTower_of_submonoid_le (LocalIntegers ell) ℚ
    p.primeCompl (nonZeroDivisors ℤ) p.primeCompl_le_nonZeroDivisors
  refine IsScalarTower.of_algebraMap_eq fun x => ?_
  change (x : ℚ) = algebraMap (LocalIntegers ell) ℚ
    (algebraMap ℤ (LocalIntegers ell) (Rat.ringOfIntegersEquiv x))
  rw [← IsScalarTower.algebraMap_apply ℤ (LocalIntegers ell) ℚ]
  exact (Rat.ringOfIntegersEquiv_apply_coe x).symm

private theorem exists_detectorNeronScheme (hloc : NeronExt.NeronDVRLocal) (A : AbVar ℚ) :
    ∃ E : Over (Spec (.of (LocalIntegers ell))),
      CToPrinted.IsNeronModelOver (LocalIntegers ell) ℚ E ∧
        Nonempty ((generic (LocalIntegers ell) ℚ).obj E ≅ A.X) := by
  letI := numberFieldAlgebra ell
  letI := numberFieldPrime_isMaximal ell
  letI := detector_isLocalization ell
  letI := detector_isScalarTower ell
  obtain ⟨E, hN, ⟨j⟩⟩ := hloc ℚ A ℚ (numberFieldPrime ell) (LocalIntegers ell)
  have hSelf : Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ)) = 𝟙 (Spec (.of ℚ)) := by
    simp
  let selfIso : (A.baseChange ℚ).X ≅ A.X :=
    eqToIso (congrArg (fun f => (Over.pullback f).obj A.X) hSelf) ≪≫
      Over.pullbackId.app A.X
  exact ⟨E, hN, ⟨j ≪≫ selfIso⟩⟩

/-- A local Néron group model whose generic fibre has the fixed equation. -/
structure LocalTarget (E₀ : WeierstrassCurve ℚ) where
  E : Over (Spec (.of (LocalIntegers ell)))
  [groupE : GrpObj E]
  neron : CToPrinted.IsNeronModelOver (LocalIntegers ell) ℚ E
  jE : (generic (LocalIntegers ell) ℚ).obj E ≅ J0Cusps.projectiveTarget E₀
  [properGenericE : IsProper ((generic (LocalIntegers ell) ℚ).obj E).hom]
  [geomIntGenericE : GeometricallyIntegral ((generic (LocalIntegers ell) ℚ).obj E).hom]

attribute [instance] LocalTarget.groupE LocalTarget.properGenericE LocalTarget.geomIntGenericE

private def localTargetOfModel (E₀ : WeierstrassCurve ℚ)
    [GrpObj (J0Cusps.projectiveTarget E₀)] {E : Over (Spec (.of (LocalIntegers ell)))}
    (hN : CToPrinted.IsNeronModelOver (LocalIntegers ell) ℚ E)
    (jE : (generic (LocalIntegers ell) ℚ).obj E ≅ J0Cusps.projectiveTarget E₀) :
    LocalTarget ell E₀ := by
  let R := LocalIntegers ell
  let A := J0Cusps.projectiveAbVar E₀
  have hMap (Y : Over (Spec (.of R))) (hY : Smooth Y.hom) :
      Function.Bijective fun f : Y ⟶ E => (generic R ℚ).map f ≫ jE.hom := by
    letI := hY
    have hj : Function.Bijective (fun f : (generic R ℚ).obj Y ⟶ (generic R ℚ).obj E =>
        f ≫ jE.hom) :=
      ⟨fun a b h => (cancel_mono jE.hom).mp h, fun f => ⟨f ≫ jE.inv, by simp⟩⟩
    exact hj.comp (hN.2.2.2.2 Y)
  let groupE := grpObjOfNeron (generic R ℚ) (fun Y => Smooth Y.hom)
    (smooth_tensorUnit _) (fun X Y hX hY => smooth_tensor X Y hX hY)
    E hN.1 (J0Cusps.projectiveTarget E₀) jE hMap
  have hpb : IsPullback jE.hom.left ((generic R ℚ).obj E).hom
      (J0Cusps.projectiveTarget E₀).hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨(Over.w jE.hom).trans (Category.comp_id _).symm⟩
  exact {
    E := E
    groupE := groupE
    neron := hN
    jE := jE
    properGenericE := MorphismProperty.of_isPullback (P := @IsProper) hpb (AbVar.proper A)
    geomIntGenericE :=
      MorphismProperty.of_isPullback (P := @GeometricallyIntegral) hpb (AbVar.geomInt A) }

/-- The existing local existence input yields a Néron model of the actual fixed
rational Weierstrass target over the detector's local ring. -/
theorem nonempty_localTarget (hloc : NeronExt.NeronDVRLocal)
    (E₀ : WeierstrassCurve ℚ) [E₀.IsElliptic] : Nonempty (LocalTarget ell E₀) := by
  obtain ⟨group, -⟩ := J0Cusps.projectiveGroup_exists E₀
  letI := group
  obtain ⟨E, hN, ⟨jE⟩⟩ := exists_detectorNeronScheme ell hloc (J0Cusps.projectiveAbVar E₀)
  exact ⟨localTargetOfModel ell E₀ hN jE⟩

#print axioms numberFieldPrime
#print axioms numberFieldAlgebra
#print axioms numberFieldPrime_isMaximal
#print axioms detector_isLocalization
#print axioms detector_isScalarTower
#print axioms exists_detectorNeronScheme
#print axioms LocalTarget
#print axioms localTargetOfModel
#print axioms nonempty_localTarget

end ZInQ.Manuscript.RC.ModelNeron
