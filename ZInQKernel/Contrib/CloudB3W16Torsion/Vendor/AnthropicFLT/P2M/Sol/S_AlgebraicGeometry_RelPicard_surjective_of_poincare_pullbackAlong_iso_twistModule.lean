/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelSubPicPresheaf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardThetaBundle
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivTwist2
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesRigidify
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_eulerChar_tensor_lineBundle_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nontrivial_H0_sectionsOf_of_le_eulerChar_sub
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_twistModule_pullbackAlong_iso_pullback
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule.AlgebraicGeometry.RelPicard
open NeronModelInfra
open GoodReductionJacobian
open AlgebraicCurve
open CategoryTheory.MonoidalCategory
open Opposite

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Spec.map_preimage Surjective Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral Scheme.Hom GeometricallyIntegral Scheme.Modules.presheaf GeometricallyIrreducible Scheme.Modules.Hom Spec IsIntegral Spec.map Scheme Scheme.Modules.Hom.app IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Spec.preimage Scheme.Modules.pullbackCongr Scheme.fromSpecResidueField_apply Scheme.Modules.pullbackId Scheme.Modules Scheme.Hom.comp_apply Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible SmoothProperCurve.FiniteMapData Scheme.TwoAffineOpenCover RelEffCartierDiv RelEffCartierDiv.twistModule RelEffCartierDiv.twistModule_def Scheme.Modules.rigidifyMapIso prodKerGraph_eq_prod Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.isInvertible_I Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one RelEffCartierDiv.exists_I_eq_prodKerGraph RelEffCartierDiv.eulerChar_tensor_lineBundle_eq Scheme.Modules.IsInvertible.nontrivial_H0_sectionsOf_of_le_eulerChar_sub Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback)
namespace RelPicard
export _root_.AlgebraicGeometry.RelPicard (baseChangeSnd postComp baseChangeSnd_comp RigidifiedLineBundle RepresentsRelSubPic fibreAt IsAlgEquivZero FibrewiseAlgEquivZero IsAlgEquivZero.of_iso algEquivZeroCut sectionIdeal RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso isAlgEquivZero_iff_eulerChar_sectionsOf_eq)
namespace AJSurj
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry

noncomputable def sectionOfGlobal {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) : M.val.sections :=
  ⟨fun U => (Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ,
   fun {U V} f => by
     show (Scheme.Modules.presheaf M).map f ((Scheme.Modules.presheaf M).map (homOfLE (le_top : U.unop ≤ ⊤)).op σ) =
       (Scheme.Modules.presheaf M).map (homOfLE (le_top : V.unop ≤ ⊤)).op σ
     have hg : (homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f = (homOfLE (le_top : V.unop ≤ ⊤)).op :=
       Subsingleton.elim _ _
     rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp, hg]⟩

theorem sectionOfGlobal_top {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) :
    (sectionOfGlobal M σ).val (op ⊤) = σ := by
  show (Scheme.Modules.presheaf M).map (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op σ = σ
  have h1 : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op ⊤) := Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id]
  rfl

theorem exists_hom_ne_zero {X : Scheme.{u}} (M : X.Modules) (σ : Γ(M, ⊤)) (hσ : σ ≠ 0) :
    ∃ s : 𝟙_ X.Modules ⟶ M, s ≠ 0 := by
  obtain ⟨s, hs⟩ : ∃ s : 𝟙_ X.Modules ⟶ M, (SheafOfModules.unitHomEquiv M) s = sectionOfGlobal M σ :=
    ⟨(SheafOfModules.unitHomEquiv M).symm (sectionOfGlobal M σ), Equiv.apply_symm_apply _ _⟩
  refine ⟨s, fun h0 => hσ ?_⟩
  have e2 : (sectionOfGlobal M σ).val (op ⊤) = σ := sectionOfGlobal_top M σ
  have e3 : (sectionOfGlobal M σ).val (op ⊤) = (Scheme.Modules.Hom.app s ⊤) (1 : Γ(X, ⊤)) := by
    rw [← hs]
    rfl
  rw [← e2, e3, h0, Scheme.Modules.Hom.zero_app]
  rfl

variable (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)

omit [IsNoetherianRing R] [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in

theorem isAlgEquivZero_of_fibrewise {k : Type u} [Field k] [IsAlgClosed k]
    {s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε s) (hM : FibrewiseAlgEquivZero M) :
    IsAlgEquivZero (pullback.snd c s) M.L := by
  have h1 := hM k (𝟙 _)
  let e : pullback c s ⟶ pullback (pullback.snd c s) (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.lift (𝟙 _) (pullback.snd c s) (by simp)
  have he : e ≫ fibreAt c s (𝟙 _) = pullback.snd c s := pullback.lift_snd _ _ _
  have hfst : e ≫ pullback.fst (pullback.snd c s) (𝟙 _) = 𝟙 _ := pullback.lift_fst _ _ _
  refine IsAlgEquivZero.of_iso ?_ (h1.pullback e he)
  exact (Scheme.Modules.pullbackComp _ _).app M.L ≪≫ (Scheme.Modules.pullbackCongr hfst).app M.L ≪≫
    (Scheme.Modules.pullbackId _).app M.L

omit [IsNoetherianRing R] [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c] in

theorem nonempty_twoAffineOpenCover (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((pullback c s).TwoAffineOpenCover) := by
  obtain ⟨𝔉, -⟩ := h𝔉 0
  obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of R ⟶ CommRingCat.of k, Spec.map φ = s :=
    ⟨Spec.preimage s, Spec.map_preimage s⟩
  letI : Algebra R k := φ.hom.toAlgebra
  exact ⟨𝔉.twoAffineOpenCover.pullback c k⟩

omit [IsNoetherianRing R] in
theorem core (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m) (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    {k : Type u} [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε s) (hM : FibrewiseAlgEquivZero M) :
    ∃ E : RelEffCartierDiv c g s, Nonempty (E.twistModule c ε ≅ M.L) := by

  haveI : IsSeparated c := inferInstance
  haveI : GeometricallyIrreducible c := inferInstance
  haveI : IsProper (pullback.snd c s) := MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd c s) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : IsIntegral (pullback c s) :=
    GeometricallyIntegral.geometrically_isIntegral (f := c) s (pullback.fst c s) (pullback.snd c s)
      (IsPullback.of_hasPullback c s)
  obtain ⟨𝒱⟩ := nonempty_twoAffineOpenCover R c ε h𝔉 s

  have h0 : IsAlgEquivZero (pullback.snd c s) M.L := isAlgEquivZero_of_fibrewise R c ε M hM
  have hχM := (isAlgEquivZero_iff_eulerChar_sectionsOf_eq k (pullback.snd c s) M.L M.isInvertible 𝒱).mp h0

  obtain ⟨hH1, hH0⟩ := Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one k
    (pullback.snd c s) g (hg k s) 𝒱

  have hεs : (s ≫ ε.1) ≫ c = s := by rw [Category.assoc, ε.2, Category.comp_id]
  obtain ⟨Eg, hEgI⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph (f := c) (g := s)
    (fun _ : Fin g => s ≫ ε.1) (fun _ => hεs)
  have hEginv : Eg.I.IsInvertible := RelEffCartierDiv.isInvertible_I Eg
  have hN : Scheme.Modules.IsInvertible (M.L ⊗ Eg.lineBundle) :=
    M.isInvertible.tensor hEginv.isInvertible_invModule
  have hχ2 := RelEffCartierDiv.eulerChar_tensor_lineBundle_eq (f := c) s Eg M.L M.isInvertible 𝒱

  have hpos : (Module.finrank k (𝒱.sectionsOf (pullback.snd c s)
        (SheafOfModules.unit (pullback c s).ringCatSheaf : (pullback c s).Modules)).H1 : ℤ)
      ≤ ((Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0 : ℤ)
          - Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H1)
        - ((Module.finrank k (𝒱.sectionsOf (pullback.snd c s)
              (SheafOfModules.unit (pullback c s).ringCatSheaf : (pullback c s).Modules)).H0 : ℤ)
            - Module.finrank k (𝒱.sectionsOf (pullback.snd c s)
              (SheafOfModules.unit (pullback c s).ringCatSheaf : (pullback c s).Modules)).H1) := by
    omega
  have hnt : Nontrivial (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0 :=
    Scheme.Modules.IsInvertible.nontrivial_H0_sectionsOf_of_le_eulerChar_sub k (pullback.snd c s) _ hN 𝒱 hpos
  obtain ⟨yv, hyv⟩ := exists_ne (0 : (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0)
  obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱 (pullback.snd c s)
    (M.L ⊗ Eg.lineBundle)
  have hσ : eΓ.symm yv ≠ 0 := fun h => hyv (by rw [← eΓ.apply_symm_apply yv, h, map_zero])
  obtain ⟨σ, hσ0⟩ := exists_hom_ne_zero (M.L ⊗ Eg.lineBundle) (eΓ.symm yv) hσ

  have hχ3u : (Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H1
      = (Module.finrank k (𝒱.sectionsOf (pullback.snd c s)
            (SheafOfModules.unit (pullback c s).ringCatSheaf : (pullback c s).Modules)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c s)
            (SheafOfModules.unit (pullback c s).ringCatSheaf : (pullback c s).Modules)).H1 + g := by
    omega
  have hχ3 : (Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (M.L ⊗ Eg.lineBundle)).H1
      = (Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (𝟙_ (pullback c s).Modules)).H0 : ℤ)
        - Module.finrank k (𝒱.sectionsOf (pullback.snd c s) (𝟙_ (pullback c s).Modules)).H1 + g := hχ3u
  obtain ⟨E, -, ⟨eE, -⟩⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq (f := c)
    s hN σ hσ0 𝒱 g hχ3

  have hEg : Eg.I = (sectionIdeal c ε s) ^ g := by
    rw [hEgI, prodKerGraph_eq_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rfl
  obtain ⟨eC⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hEginv
  have eI : ((sectionIdeal c ε s) ^ g).module ≅ Eg.I.module := eqToIso (by rw [hEg])
  have i1 : E.lineBundle ⊗ ((sectionIdeal c ε s) ^ g).module ≅ M.L :=
    (eE.symm ⊗ᵢ eI) ≪≫ (α_ _ _ _) ≪≫ (Iso.refl _ ⊗ᵢ eC) ≪≫ (ρ_ _)
  refine ⟨E, ⟨?_⟩⟩
  rw [RelEffCartierDiv.twistModule_def]
  exact Scheme.Modules.rigidifyMapIso _ _ i1 ≪≫ (RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified M).some

omit [IsNoetherianRing R] in
theorem main
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {Y : Scheme.{u}} {y : Y ⟶ Spec (CommRingCat.of R)} {𝒟 : RelEffCartierDiv c g y} (hU : 𝒟.IsUniversal)
    (aj : Y ⟶ D.P) (haj : aj ≫ D.toBase = y)
    (hclass : Nonempty ((h.poincare.pullbackAlong (⟨aj, haj⟩ : SchemeHomOver y D.toBase)).L ≅ 𝒟.twistModule c ε)) :
    Surjective aj := by
  haveI : IsSeparated c := inferInstance
  refine ⟨fun z => ?_⟩

  let kz := D.P.residueField z
  let k : Type u := AlgebraicClosure kz
  let ι : Spec (CommRingCat.of k) ⟶ D.P :=
    Spec.map (CommRingCat.ofHom (algebraMap kz k)) ≫ D.P.fromSpecResidueField z
  let s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R) := ι ≫ D.toBase
  let tb : SchemeHomOver s D.toBase := ⟨ι, rfl⟩

  let M : RigidifiedLineBundle c ε s := h.poincare.pullbackAlong tb
  have hM : FibrewiseAlgEquivZero M := (algEquivZeroCut c ε).pullback_mem _ _ tb _ h.poincare_mem

  obtain ⟨E, ⟨eE⟩⟩ := core R c ε h𝔉 g hg s M hM

  let y₀ : Spec (CommRingCat.of k) ⟶ Y := hU.lift E
  have hy₀ : y₀ ≫ y = s := hU.lift_comp E
  let ψ : SchemeHomOver s y := ⟨y₀, hy₀⟩
  have hE : 𝒟.pullbackAlong y₀ hy₀ = E := hU.pullbackAlong_lift E
  let ajO : SchemeHomOver y D.toBase := ⟨aj, haj⟩

  have key : Nonempty ((h.poincare.pullbackAlong (postComp ajO ψ)).L ≅ (h.poincare.pullbackAlong tb).L) := by
    obtain ⟨ecl⟩ := hclass
    obtain ⟨etw⟩ := RelEffCartierDiv.nonempty_twistModule_pullbackAlong_iso_pullback c ε ψ 𝒟
    exact ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_comp c ajO ψ).symm).app h.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp _ _).app h.poincare.L).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c ψ)).mapIso ecl ≪≫ etw.symm ≪≫
      eqToIso (congrArg (fun D' => RelEffCartierDiv.twistModule c ε D') hE) ≪≫ eE⟩
  have heq : postComp ajO ψ = tb := h.ext_of_iso s _ _ key
  have hcomp : y₀ ≫ aj = ι := congrArg Subtype.val heq
  refine ⟨y₀ (IsLocalRing.closedPoint k), ?_⟩
  rw [← Scheme.Hom.comp_apply, hcomp]
  exact Scheme.fromSpecResidueField_apply z _

end AlgebraicGeometry.RelPicard.AJSurj
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_surjective_of_poincare_pullbackAlong_iso_twistModule.AlgebraicGeometry.RelPicard
open NeronModelInfra
open GoodReductionJacobian
open AlgebraicCurve
open CategoryTheory.MonoidalCategory

theorem solution
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g : ℕ)
    (hg : ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    {Y : Scheme.{u}} {y : Y ⟶ Spec (CommRingCat.of R)} {𝒟 : RelEffCartierDiv c g y} (hU : 𝒟.IsUniversal)
    (aj : Y ⟶ D.P) (haj : aj ≫ D.toBase = y)
    (hclass : Nonempty ((h.poincare.pullbackAlong (⟨aj, haj⟩ : SchemeHomOver y D.toBase)).L ≅ 𝒟.twistModule c ε)) :
    Surjective aj :=
  AlgebraicGeometry.RelPicard.AJSurj.main R c ε h𝔉 g hg D h hU aj haj hclass
