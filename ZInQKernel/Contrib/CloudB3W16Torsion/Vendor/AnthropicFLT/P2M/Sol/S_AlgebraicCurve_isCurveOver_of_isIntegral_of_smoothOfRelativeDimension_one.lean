/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry AlgebraicCurve Opposite

universe u v

namespace SmoothModelFunctionField

theorem stageA {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsIntegral C]
    [SmoothOfRelativeDimension 1 c] :
    letI := (baseToFunctionField c).toAlgebra
    Algebra.EssFiniteType K C.functionField ∧
      Module.rank C.functionField Ω[C.functionField⁄K] = 1 := by
  letI algKF : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c) x
  haveI : Nonempty V := ⟨⟨x, hxV⟩⟩

  obtain rfl : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have : y = c.base x := Subsingleton.elim _ _
    rw [this]; exact e hxV

  let eK : Γ(Spec (CommRingCat.of K), ⊤) ≃+* K := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv
  letI algRA : Algebra Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V) := (c.appLE ⊤ V e).hom.toAlgebra
  have hstdA : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V) :=
    hstd
  letI algKR : Algebra K Γ(Spec (CommRingCat.of K), ⊤) := eK.symm.toRingHom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 K Γ(Spec (CommRingCat.of K), ⊤) :=
    .of_algebraMap_bijective eK.symm.bijective
  letI algKA : Algebra K Γ(C, V) :=
    ((algebraMap Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V)).comp
      (algebraMap K Γ(Spec (CommRingCat.of K), ⊤))).toAlgebra
  haveI : IsScalarTower K Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI hKA : Algebra.IsStandardSmoothOfRelativeDimension (1 + 0) K Γ(C, V) :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans 0 1 K Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V)

  haveI : IsFractionRing Γ(C, V) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C V hV
  haveI : IsScalarTower K Γ(C, V) C.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    change baseToFunctionField c k =
      (C.germToFunctionField V).hom ((c.appLE ⊤ V e).hom (eK.symm k))
    simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appLE,
      Scheme.germToFunctionField, CommRingCat.hom_comp]
    rw [TopCat.Presheaf.germ_res_apply]
    rfl

  haveI := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 1 + 0) (R := K)
    (S := Γ(C, V))
  haveI : Algebra.EssFiniteType Γ(C, V) C.functionField :=
    Algebra.EssFiniteType.of_isLocalization C.functionField (nonZeroDivisors Γ(C, V))
  refine ⟨Algebra.EssFiniteType.comp K Γ(C, V) C.functionField, ?_⟩

  haveI : Algebra.FormallyEtale Γ(C, V) C.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(C, V))
  have h := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K Γ(C, V)
    C.functionField).lift_rank_eq
  rw [Module.rank_baseChange,
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (1 + 0)] at h
  simpa using h.symm

theorem rank_kaehler_adjoin {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
    (s : Finset F) (hs : AlgebraicIndependent K ((↑) : s → F)) :
    Module.rank (IntermediateField.adjoin K (Set.range ((↑) : s → F)))
      Ω[IntermediateField.adjoin K (Set.range ((↑) : s → F))⁄K] = Fintype.card s := by
  set L := IntermediateField.adjoin K (Set.range ((↑) : s → F))
  let e : FractionRing (MvPolynomial s K) ≃ₐ[K] L := hs.aevalEquivField
  letI : Algebra (MvPolynomial s K) L :=
    ((e : FractionRing (MvPolynomial s K) →ₐ[K] L).comp
      (IsScalarTower.toAlgHom K (MvPolynomial s K) (FractionRing (MvPolynomial s K)))).toAlgebra
  haveI : IsScalarTower K (MvPolynomial s K) L :=
    IsScalarTower.of_algebraMap_eq fun k => by
      simp [RingHom.algebraMap_toAlgebra]
  have e' : FractionRing (MvPolynomial s K) ≃ₐ[MvPolynomial s K] L :=
    { e.toRingEquiv with commutes' := fun p => rfl }
  haveI : IsFractionRing (MvPolynomial s K) L :=
    IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors (MvPolynomial s K)) e'
  haveI : Algebra.FormallyEtale (MvPolynomial s K) L :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors (MvPolynomial s K))
  haveI : Module.Free (MvPolynomial s K) Ω[MvPolynomial s K⁄K] :=
    Module.Free.of_basis (KaehlerDifferential.mvPolynomialBasis K s)
  have eΩ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K (MvPolynomial s K) L
  have h := eΩ.lift_rank_eq
  rw [Module.rank_baseChange, rank_eq_card_basis (KaehlerDifferential.mvPolynomialBasis K s)] at h
  simpa using h.symm

theorem isCurveOver_of_rank_eq_one {K : Type u} [Field K] [PerfectField K] {F : Type v}
    [Field F] [Algebra K F] [Algebra.EssFiniteType K F] (hΩ : Module.rank F Ω[F⁄K] = 1) :
    IsCurveOver K F := by
  obtain ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField K F
  have hr : (s : Set F) = Set.range ((↑) : s → F) := by ext; simp
  rw [hr] at hsep
  have hcard : (Fintype.card s : Cardinal.{v}) = 1 := by
    haveI : Algebra.FormallyEtale (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F :=
      Algebra.FormallyEtale.of_isSeparable _ F
    have h1 := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K
      (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F).lift_rank_eq
    rw [Module.rank_baseChange, rank_kaehler_adjoin s hs.1, hΩ] at h1
    simpa using h1
  have hs1 : s.card = 1 := by
    rw [Fintype.card_coe] at hcard
    exact_mod_cast hcard
  obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp hs1
  have hx : Set.range ((↑) : ({x} : Finset F) → F) = {x} := by ext; simp
  rw [hx] at hsep
  have htr : Transcendental K x := hs.1.transcendental ⟨x, Finset.mem_singleton_self x⟩
  haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F := by
    have := hs.isAlgebraic_field; rwa [hx] at this
  haveI : Algebra.EssFiniteType (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.EssFiniteType.of_comp K _ F
  exact AlgebraicCurve.isCurveOver_of_transcendental htr
    (Algebra.finite_of_essFiniteType_of_isAlgebraic
      (F := IntermediateField.adjoin K ({x} : Set F)) (E := F)) hsep

theorem rank_kaehler_eq_one_of_algEquiv {K : Type u} [Field K] {F : Type v} [Field F]
    [Algebra K F] {L : Type*} [Field L] [Algebra K L] (e : F ≃ₐ[K] L)
    (h : Module.rank L Ω[L⁄K] = 1) : Module.rank F Ω[F⁄K] = 1 := by
  letI : Algebra L F := (e.symm : L →ₐ[K] F).toRingHom.toAlgebra
  haveI : IsScalarTower K L F :=
    IsScalarTower.of_algebraMap_eq fun k => by simp [RingHom.algebraMap_toAlgebra]
  have e' : L ≃ₐ[L] F := { e.symm.toRingEquiv with commutes' := fun l => rfl }
  haveI : Algebra.FormallyEtale L L := Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  haveI : Algebra.FormallyEtale L F := Algebra.FormallyEtale.of_equiv e'
  have h1 := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K L F).lift_rank_eq
  rw [Module.rank_baseChange, h] at h1
  simpa using h1.symm

theorem assembly {K : Type u} [Field K] [PerfectField K] {F : Type v} [Field F] [Algebra K F]
    {C : AlgebraicGeometry.Scheme.{u}} (c : C ⟶ AlgebraicGeometry.Spec (.of K))
    [AlgebraicGeometry.IsIntegral C]
    (φ : F ≃+* C.functionField) (hφ : ∀ a : K, φ (algebraMap K F a) = baseToFunctionField c a)
    (hA1 : letI := (baseToFunctionField c).toAlgebra; Algebra.EssFiniteType K C.functionField)
    (hA2 : letI := (baseToFunctionField c).toAlgebra;
      Module.rank C.functionField Ω[C.functionField⁄K] = 1) :
    IsCurveOver K F := by
  letI := (baseToFunctionField c).toAlgebra
  let e : F ≃ₐ[K] C.functionField := AlgEquiv.ofRingEquiv (f := φ) hφ
  haveI : Algebra.EssFiniteType K F := (Algebra.EssFiniteType.iff_of_algEquiv e).mpr hA1
  exact isCurveOver_of_rank_eq_one (rank_kaehler_eq_one_of_algEquiv e hA2)

end SmoothModelFunctionField

theorem solution
    {K : Type u} [Field K] [PerfectField K] {F : Type v} [Field F] [Algebra K F]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsIntegral C]
    [SmoothOfRelativeDimension 1 c] (φ : F ≃+* C.functionField)
    (hφ : ∀ a : K, φ (algebraMap K F a) = baseToFunctionField c a) :
    IsCurveOver K F :=
  SmoothModelFunctionField.assembly c φ hφ (SmoothModelFunctionField.stageA c).1
    (SmoothModelFunctionField.stageA c).2
