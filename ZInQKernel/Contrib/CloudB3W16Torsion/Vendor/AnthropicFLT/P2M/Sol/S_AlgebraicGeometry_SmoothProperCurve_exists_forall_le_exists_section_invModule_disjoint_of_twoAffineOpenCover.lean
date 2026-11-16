/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_SmoothProperCurve_exists_forall_le_exists_section_invModule_disjoint_of_twoAffineOpenCover. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_surjective_unit_app_top_invModule_pow_ker
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothProperCurve_exists_section_pullback_invModule_pow_ker_notMem_support_of_twoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_comap_zeroSchemeIdeal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_forall_le_exists_section_invModule_disjoint_of_twoAffineOpenCover

set_option autoImplicit false

universe u

open scoped TensorProduct
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_forall_le_exists_section_invModule_disjoint_of_twoAffineOpenCover.AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve
open P2MW.S_AlgebraicGeometry_SmoothProperCurve_exists_forall_le_exists_section_invModule_disjoint_of_twoAffineOpenCover.AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra
open CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Modules.hom_ext Scheme.Modules.Hom.app_smul Surjective Scheme.IdealSheafData.support_comap SmoothOfRelativeDimension Scheme.Modules.pushforward IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Spec Scheme Scheme.Modules.pullbackPushforwardAdjunction Scheme.Modules Scheme.IdealSheafData Scheme.TwoAffineOpenCover Scheme.TwoAffineOpenCover.specMap Scheme.Modules.toUnitSection Scheme.Modules.ofUnitSection Scheme.Modules.ofUnitSection_toUnitSection Scheme.Modules.ofUnitSection_injective Scheme.Modules.ofUnitSection_map Scheme.Modules.ofUnitSection_smul Scheme.Modules.zeroSchemeIdeal Scheme.Modules.pullbackSection Scheme.Modules.pullbackSection_def Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover SmoothProperCurve.surjective_unit_app_top_invModule_pow_ker SmoothProperCurve.exists_section_pullback_invModule_pow_ker_notMem_support_of_twoAffineOpenCover Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal Scheme.Hom.isInvertible_ker_of_comp_eq_id)
namespace SmoothProperCurve
export _root_.AlgebraicGeometry.SmoothProperCurve (exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover specMap surjective_unit_app_top_invModule_pow_ker exists_section_pullback_invModule_pow_ker_notMem_support_of_twoAffineOpenCover)
namespace LiftSectionAux
open AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry

variable {X Y : Scheme.{u}}

lemma app_map {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : V ⟶ U) (x : Γ(M, U)) :
    φ.app V (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app U x) := by
  simpa using ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.op) x

lemma hom_ext_of_app_top {N : X.Modules} {f g : 𝟙_ X.Modules ⟶ N}
    (h : f.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = g.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1)) :
    f = g := by
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  have hx : x = (Scheme.Modules.ofUnitSection U x) •
      (𝟙_ X.Modules).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (Scheme.Modules.toUnitSection ⊤ 1) := by
    apply Scheme.Modules.ofUnitSection_injective
    rw [Scheme.Modules.ofUnitSection_smul, Scheme.Modules.ofUnitSection_map,
      Scheme.Modules.ofUnitSection_toUnitSection, map_one, mul_one]
  rw [hx, Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, app_map, app_map, h]

lemma exists_hom_app_top_eq {N : X.Modules} (s₀ : Γ(N, ⊤)) :
    ∃ s : 𝟙_ X.Modules ⟶ N, s.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1) = s₀ := by
  let σ : N.val.sections := PresheafOfModules.sectionsMk
    (fun U => N.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op s₀)
    (by
      intro U V f
      change N.presheaf.map f (N.presheaf.map _ s₀) = _
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      exact congrFun (congrArg (fun j => ⇑(ConcreteCategory.hom (N.presheaf.map j)))
        (Subsingleton.elim _ _)) s₀)
  refine ⟨(SheafOfModules.unitHomEquiv N).symm σ, ?_⟩
  have h := SheafOfModules.unitHomEquiv_apply_coe N ((SheafOfModules.unitHomEquiv N).symm σ)
    (Opposite.op ⊤)
  rw [Equiv.apply_symm_apply] at h
  have h' : σ.val (Opposite.op ⊤) = s₀ := by
    change N.presheaf.map _ s₀ = s₀
    have : (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
    rw [this, N.presheaf.map_id]
    rfl
  change ((SheafOfModules.unitHomEquiv N).symm σ).val.app (Opposite.op ⊤) (1 : Γ(X, ⊤)) = s₀
  exact h.symm.trans h'

lemma exists_pullbackSection_eq (F : X ⟶ Y) (M : Y.Modules)
    (hsurj : Function.Surjective
      (((Scheme.Modules.pullbackPushforwardAdjunction F).unit.app M).app ⊤).hom)
    (t' : 𝟙_ X.Modules ⟶ (Scheme.Modules.pullback F).obj M) :
    ∃ s : 𝟙_ Y.Modules ⟶ M, Scheme.Modules.pullbackSection F s = t' := by
  set adj := Scheme.Modules.pullbackPushforwardAdjunction F with hadj
  let t : (Scheme.Modules.pullback F).obj (𝟙_ Y.Modules) ⟶ (Scheme.Modules.pullback F).obj M :=
    (Scheme.Modules.pullbackUnitIso F).hom ≫ t'
  let tflat : 𝟙_ Y.Modules ⟶ (Scheme.Modules.pushforward F).obj ((Scheme.Modules.pullback F).obj M) :=
    adj.homEquiv _ _ t
  obtain ⟨s₀, hs₀⟩ := hsurj (tflat.app ⊤ (Scheme.Modules.toUnitSection ⊤ 1))
  obtain ⟨s, hs⟩ := exists_hom_app_top_eq (N := M) s₀
  refine ⟨s, ?_⟩
  have h1 : s ≫ adj.unit.app M = tflat := by
    apply hom_ext_of_app_top
    rw [Scheme.Modules.Hom.comp_app, CategoryTheory.ConcreteCategory.comp_apply, hs]
    exact hs₀
  have h2 : adj.homEquiv _ _ ((Scheme.Modules.pullback F).map s) = s ≫ adj.unit.app M := by
    rw [Adjunction.homEquiv_apply]
    exact (adj.unit.naturality s).symm
  have h3 : (Scheme.Modules.pullback F).map s = t := (adj.homEquiv _ _).injective (h2.trans h1)
  rw [Scheme.Modules.pullbackSection_def]
  exact (congrArg (fun φ => (Scheme.Modules.pullbackUnitIso F).inv ≫ φ) h3).trans (by simp [t])

end AlgebraicGeometry.SmoothProperCurve.LiftSectionAux

open AlgebraicGeometry.SmoothProperCurve.LiftSectionAux in
theorem solution
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (𝒱 : C.TwoAffineOpenCover) :
    ∃ m₁ : ℕ, ∀ m : ℕ, m₁ ≤ m →
      ∃ s : 𝟙_ C.Modules ⟶ (ε.1.ker ^ m).invModule,
        ∀ x ∈ Set.range ε.1.base, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by
  classical
  obtain ⟨g, hg⟩ :=
    AlgebraicGeometry.SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_twoAffineOpenCover
      R c 𝒱
  refine ⟨2 * g + 1, fun m hm => ?_⟩

  let k : Type u := IsLocalRing.ResidueField R
  let M : C.Modules := (ε.1.ker ^ m).invModule
  let F := pullback.fst c (Scheme.TwoAffineOpenCover.specMap R k)

  obtain ⟨sbar, hsbar⟩ :=
    AlgebraicGeometry.SmoothProperCurve.exists_section_pullback_invModule_pow_ker_notMem_support_of_twoAffineOpenCover
      R c ε g hg m (by omega) (by omega) 𝒱 k

  have hA : Function.Surjective (algebraMap R k) := IsLocalRing.residue_surjective
  have hsurj :=
    AlgebraicGeometry.SmoothProperCurve.surjective_unit_app_top_invModule_pow_ker R c ε g hg m (by omega) 𝒱 k hA
  obtain ⟨s, hs⟩ := exists_pullbackSection_eq F M hsurj sbar
  refine ⟨s, ?_⟩

  have hker : ε.1.ker.IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := c) ε.1 ε.2
  have hM : Scheme.Modules.IsInvertible M := (hker.pow m).isInvertible_invModule

  let z : Spec (CommRingCat.of k) ⟶ pullback c (Scheme.TwoAffineOpenCover.specMap R k) :=
    pullback.lift (Scheme.TwoAffineOpenCover.specMap R k ≫ ε.1) (𝟙 _)
      (by rw [Category.assoc, ε.2, Category.id_comp, Category.comp_id])
  have hz := hsbar z (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hzF : z ≫ F = Scheme.TwoAffineOpenCover.specMap R k ≫ ε.1 := pullback.lift_fst _ _ _
  have hFz : F.base (z.base (IsLocalRing.closedPoint k)) = ε.1.base (IsLocalRing.closedPoint R) := by
    change (z ≫ F).base (IsLocalRing.closedPoint k) = _
    rw [hzF]
    change ε.1.base ((Scheme.TwoAffineOpenCover.specMap R k).base (IsLocalRing.closedPoint k)) = _
    congr 1
    haveI : IsLocalHom (algebraMap R k) := inferInstanceAs (IsLocalHom (IsLocalRing.residue R))
    exact IsLocalRing.comap_closedPoint (algebraMap R k)

  have hx₀ : ε.1.base (IsLocalRing.closedPoint R) ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by
    intro hmem
    apply hz
    rw [← hs, ← Scheme.Modules.IsInvertible.comap_zeroSchemeIdeal F hM s,
      Scheme.IdealSheafData.support_comap]
    show F.base (z.base (IsLocalRing.closedPoint k)) ∈ ((Scheme.Modules.zeroSchemeIdeal s).support : Set C)
    rw [hFz]
    exact hmem

  rintro x ⟨p, rfl⟩ hx
  apply hx₀
  have hsp : ε.1.base p ⤳ ε.1.base (IsLocalRing.closedPoint R) :=
    (IsLocalRing.specializes_closedPoint p).map ε.1.base.hom.continuous
  exact hsp.mem_closed (Scheme.Modules.zeroSchemeIdeal s).support.isClosed hx
