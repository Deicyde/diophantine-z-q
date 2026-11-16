/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAbelJacobiFamily
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nontrivial_H0_sectionsOf_of_le_eulerChar_sub
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_eulerChar_tensor_lineBundle_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_H0
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_of_iso_pointsSubBasepoint
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_isAlgClosed
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open Opposite
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq.AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open P2MW.S_AlgebraicGeometry_RelPicard_isAlgEquivZero_iff_eulerChar_sectionsOf_eq.AlgebraicGeometry.RelPicard
open NeronModelInfra
open GoodReductionJacobian

namespace AlgebraicGeometry
export AlgebraicGeometry (Scheme.Modules.Hom.zero_app SmoothOfRelativeDimension IsProper Scheme.Modules.pullback GeometricallyIntegral.geometrically_isIntegral GeometricallyIntegral Scheme.Modules.presheaf GeometricallyIrreducible Scheme.Modules.Hom QuasiCompact LocallyOfFiniteType Spec IsIntegral Scheme Scheme.Modules.Hom.app QuasiCompact.compactSpace_of_compactSpace IsSeparated smoothOfRelativeDimension_isStableUnderBaseChange Scheme.Modules geometrically Scheme.IdealSheafData Scheme.Modules.IsInvertible Scheme.Modules.isInvertible_unit RelPicard.IsAlgEquivZero RelEffCartierDiv RelEffCartierDiv.ofPoint RelEffCartierDiv.ofPoint_I Scheme.IdealSheafData.IsInvertible Scheme.Modules.pullbackTensorUnitObjIso RelEffCartierDiv.isInvertible_I Scheme.TwoAffineOpenCover prodKerGraph prodKerGraph_eq_prod Scheme.Modules.IsInvertible.nontrivial_H0_sectionsOf_of_le_eulerChar_sub RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed RelEffCartierDiv.exists_I_eq_prodKerGraph RelPicard.IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq RelEffCartierDiv.eulerChar_tensor_lineBundle_eq Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 RelPicard.nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule geometricallyIntegral_of_isAlgClosed exists_over_hom_base_closedPoint_eq_of_isClosed_singleton)
namespace RelPicard
export AlgebraicGeometry.RelPicard (IsAlgEquivZero Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso pointsSubBasepointModule IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule IsAlgEquivZero.of_iso_pointsSubBasepoint)
namespace AlgzNum
open AlgebraicGeometry.RelPicard
open AlgebraicGeometry

theorem twoAffineOpenCover_ext {X : Scheme.{u}} {𝒱 𝒲 : X.TwoAffineOpenCover}
    (h0 : 𝒱.U0 = 𝒲.U0) (h1 : 𝒱.U1 = 𝒲.U1) : 𝒱 = 𝒲 := by
  obtain ⟨U0, U1, p1, p2, p3, p4⟩ := 𝒱
  obtain ⟨U0', U1', q1, q2, q3, q4⟩ := 𝒲
  change U0 = U0' at h0
  change U1 = U1' at h1
  subst h0
  subst h1
  rfl

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

theorem chi_pts
    {k : Type u} [Field k] [IsAlgClosed k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsProper a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a)
    (𝒱A : A.TwoAffineOpenCover) {L : A.Modules}
    (hL : Scheme.Modules.IsInvertible L)
    (hχ : (Module.finrank k (𝒱A.sectionsOf a L).H0 : ℤ) - Module.finrank k (𝒱A.sectionsOf a L).H1 =
        (Module.finrank k (𝒱A.sectionsOf a (𝟙_ A.Modules)).H0 : ℤ) - Module.finrank k (𝒱A.sectionsOf a (𝟙_ A.Modules)).H1) :
    ∃ Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a),
      Nonempty ((Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L ≅ pointsSubBasepointModule (a := a) ε Ps) := by

  haveI : IsSeparated a := inferInstance
  haveI : GeometricallyIrreducible a := inferInstance
  haveI : IsProper (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) :=
    MorphismProperty.pullback_snd (P := @IsProper) _ _ inferInstance
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange 1
  haveI : SmoothOfRelativeDimension 1 (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) :=
    MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : IsIntegral (pullback a (𝟙 (Spec (CommRingCat.of k)))) :=
    GeometricallyIntegral.geometrically_isIntegral (f := a) (𝟙 (Spec (CommRingCat.of k)))
      (pullback.fst a (𝟙 _)) (pullback.snd a (𝟙 _)) (IsPullback.of_hasPullback a (𝟙 _))
  haveI : IsIso (pullback.fst a (𝟙 (Spec (CommRingCat.of k)))) := inferInstance

  let φ : pullback a (𝟙 (Spec (CommRingCat.of k))) ≅ A := asIso (pullback.fst a (𝟙 (Spec (CommRingCat.of k))))
  have hφ : φ.hom ≫ a = pullback.snd a (𝟙 (Spec (CommRingCat.of k))) := by
    show pullback.fst a (𝟙 (Spec (CommRingCat.of k))) ≫ a = pullback.snd a (𝟙 (Spec (CommRingCat.of k)))
    exact pullback.condition.trans (Category.comp_id _)
  let L' : (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules :=
    (Scheme.Modules.pullback (pullback.fst a (𝟙 (Spec (CommRingCat.of k))))).obj L
  have hL' : Scheme.Modules.IsInvertible L' := hL.pullback _
  obtain ⟨𝒱, hU0, hU1, ⟨eH0u⟩, ⟨eH1u⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) a φ hφ 𝒱A (𝟙_ A.Modules)
      (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)
      (Scheme.Modules.pullbackTensorUnitObjIso (pullback.fst a (𝟙 (Spec (CommRingCat.of k))))).symm
  obtain ⟨𝒱₂, hU0₂, hU1₂, ⟨eH0L⟩, ⟨eH1L⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) a φ hφ 𝒱A L L' (Iso.refl _)
  have h𝒱 : 𝒱₂ = 𝒱 := twoAffineOpenCover_ext (hU0₂.trans hU0.symm) (hU1₂.trans hU1.symm)
  subst h𝒱

  have n1 := eH0u.finrank_eq
  have n2 := eH1u.finrank_eq
  have n3 := eH0L.finrank_eq
  have n4 := eH1L.finrank_eq

  let d : ℕ := Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k))))
    (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)).H1
  obtain ⟨E, hEI⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph (f := a) (g := 𝟙 (Spec (CommRingCat.of k)))
    (fun _ : Fin d => ε.1) (fun _ => ε.2)
  have hEinv : E.I.IsInvertible := RelEffCartierDiv.isInvertible_I E
  have hLE : Scheme.Modules.IsInvertible (L' ⊗ E.lineBundle) := hL'.tensor hEinv.isInvertible_invModule
  have hχ2 := RelEffCartierDiv.eulerChar_tensor_lineBundle_eq (f := a) (𝟙 (Spec (CommRingCat.of k))) E L' hL' 𝒱₂

  have hpos : (Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k))))
        (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)).H1 : ℤ)
      ≤ ((Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle)).H0 : ℤ)
          - Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle)).H1)
        - ((Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k))))
              (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)).H0 : ℤ)
            - Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k))))
              (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)).H1) := by
    omega
  have hnt : Nontrivial (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle)).H0 :=
    Scheme.Modules.IsInvertible.nontrivial_H0_sectionsOf_of_le_eulerChar_sub k
      (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle) hLE 𝒱₂ hpos
  obtain ⟨y, hy⟩ := exists_ne (0 : (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle)).H0)
  obtain ⟨eΓ, -⟩ := Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_H0 𝒱₂
    (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle)
  have hσ : eΓ.symm y ≠ 0 := fun h => hy (by rw [← eΓ.apply_symm_apply y, h, map_zero])
  obtain ⟨s, hs⟩ := exists_hom_ne_zero (L' ⊗ E.lineBundle) (eΓ.symm y) hσ

  have hχ3 : (Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle)).H0 : ℤ)
        - Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k)))) (L' ⊗ E.lineBundle)).H1
      = (Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k))))
            (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)).H0 : ℤ)
        - Module.finrank k (𝒱₂.sectionsOf (pullback.snd a (𝟙 (Spec (CommRingCat.of k))))
            (𝟙_ (pullback a (𝟙 (Spec (CommRingCat.of k)))).Modules)).H1 + d := by
    omega
  obtain ⟨D, -, ⟨eD, -⟩⟩ := RelEffCartierDiv.exists_I_eq_zeroSchemeIdeal_of_eulerChar_eq (f := a)
    (𝟙 (Spec (CommRingCat.of k))) hLE s hs 𝒱₂ d hχ3

  obtain ⟨P, hP, hDI⟩ := RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed D

  have hE : E.I = (RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ d := by
    rw [hEI, prodKerGraph_eq_prod, Finset.prod_const, Finset.card_univ, Fintype.card_fin, RelEffCartierDiv.ofPoint_I]
  obtain ⟨eE⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso hEinv
  obtain ⟨eT⟩ := RelPicard.nonempty_invModule_prodKerGraph_tensor_module_pow_iso_pointsSubBasepointModule ε P hP
  have hcast : D.lineBundle ⊗ E.I.module =
      (prodKerGraph a P hP).invModule ⊗ ((RelEffCartierDiv.ofPoint a ε.1 ε.2).I ^ d).module := by
    show D.I.invModule ⊗ E.I.module = _
    rw [hDI, hE]
  refine ⟨List.ofFn fun i => (⟨P i, hP i⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a), ⟨?_⟩⟩
  exact (ρ_ L').symm ≪≫ whiskerLeftIso L' eE.symm ≪≫ (α_ L' E.I.invModule E.I.module).symm ≪≫
    whiskerRightIso eD E.I.module ≪≫ eqToIso hcast ≪≫ eT

theorem exists_schemeHomOver {k : Type u} [Field k] [IsAlgClosed k] {A : Scheme.{u}} (a : A ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType a] [CompactSpace A] [Nonempty A] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) := by
  obtain ⟨V, -, hne, hcl, hmin⟩ :=
    IsClosed.exists_minimal_nonempty_closed_subset (isClosed_univ : IsClosed (Set.univ : Set A)) Set.univ_nonempty
  obtain ⟨x, rfl⟩ := minimal_nonempty_closed_eq_singleton hcl hne hmin
  obtain ⟨z, -⟩ := AlgebraicGeometry.exists_over_hom_base_closedPoint_eq_of_isClosed_singleton k a x hcl
  exact ⟨⟨z.left, Over.w z⟩⟩

theorem eulerChar_eq_of_isAlgEquivZero
    (K : Type u) [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K)) [IsProper x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover) (h : IsAlgEquivZero x M) :
    (Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1 =
      (Module.finrank K (𝒱.sectionsOf x (𝟙_ X.Modules)).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x (𝟙_ X.Modules)).H1 := by
  have hχA := RelPicard.IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq x 𝒱 M (𝟙_ X.Modules) hM
    (Scheme.Modules.isInvertible_unit X) h

  let φ : pullback x (𝟙 (Spec (CommRingCat.of K))) ≅ X := asIso (pullback.fst x (𝟙 (Spec (CommRingCat.of K))))
  have hφ : φ.hom ≫ x = pullback.snd x (𝟙 (Spec (CommRingCat.of K))) :=
    pullback.condition.trans (Category.comp_id _)
  obtain ⟨𝒱₂, hU0₂, hU1₂, ⟨e0⟩, ⟨e1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (pullback.snd x (𝟙 (Spec (CommRingCat.of K)))) x φ hφ 𝒱 (M ⊗ 𝟙_ X.Modules)
      ((Scheme.Modules.pullback (pullback.fst x (𝟙 (Spec (CommRingCat.of K))))).obj M)
      ((Scheme.Modules.pullback (pullback.fst x (𝟙 (Spec (CommRingCat.of K))))).mapIso (ρ_ M).symm)
  obtain ⟨𝒱₃, hU0₃, hU1₃, ⟨e0'⟩, ⟨e1'⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso
      (pullback.snd x (𝟙 (Spec (CommRingCat.of K)))) x φ hφ 𝒱 M
      ((Scheme.Modules.pullback (pullback.fst x (𝟙 (Spec (CommRingCat.of K))))).obj M) (Iso.refl _)
  have h𝒱 : 𝒱₃ = 𝒱₂ := twoAffineOpenCover_ext (hU0₃.trans hU0₂.symm) (hU1₃.trans hU1₂.symm)
  subst h𝒱
  have n1 := e0.finrank_eq
  have n2 := e1.finrank_eq
  have n3 := e0'.finrank_eq
  have n4 := e1'.finrank_eq
  omega

end AlgebraicGeometry.RelPicard.AlgzNum

open AlgebraicGeometry.RelPicard.AlgzNum in

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover) :
    IsAlgEquivZero x M ↔
      (Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1 =
        (Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 : ℤ) -
          Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 := by
  refine ⟨fun h => eulerChar_eq_of_isAlgEquivZero K x M hM 𝒱 h, fun hχ => ?_⟩
  haveI : GeometricallyIntegral x := AlgebraicGeometry.geometricallyIntegral_of_isAlgClosed x
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace x
  obtain ⟨ε⟩ := exists_schemeHomOver x
  obtain ⟨Ps, ⟨e⟩⟩ := chi_pts ε 𝒱 hM hχ
  exact IsAlgEquivZero.of_iso_pointsSubBasepoint ε Ps e
