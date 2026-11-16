/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.CategoryTheory.Adjunction.Mates
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_dual_iso_module_zeroSchemeIdeal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_isIso_ev_app_and_isIso_curry_braiding_ev
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iso_invModule_zeroSchemeIdeal

set_option autoImplicit false

universe v u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

section MC
open CategoryTheory.MonoidalClosed
open CategoryTheory.BraidedCategory

namespace ZDIsoMC

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]

def toBidual (M : C) : M ⟶ (ihom ((ihom M).obj (𝟙_ C))).obj (𝟙_ C) :=
  MonoidalClosed.curry ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C))

omit [BraidedCategory C] in

theorem unitIsoSelf_inv (X : C) :
    (MonoidalClosed.unitIsoSelf X).inv = MonoidalClosed.curry (λ_ X).hom := by
  have h := unit_conjugateEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C).hom X
  dsimp at h
  erw [Category.id_comp] at h
  change (conjugateEquiv (Adjunction.id (C := C)) (ihom.adjunction (𝟙_ C))
    (leftUnitorNatIso C).hom).app X = _
  rw [h, MonoidalClosed.curry_eq]
  rfl

omit [BraidedCategory C] in

theorem uncurry_eq_of_comp_unitIsoSelf_hom {X Y : C} (k : Y ⟶ (ihom (𝟙_ C)).obj X) (m : Y ⟶ X)
    (h : k ≫ (MonoidalClosed.unitIsoSelf X).hom = m) :
    MonoidalClosed.uncurry k = (λ_ Y).hom ≫ m := by
  have hk : k = m ≫ MonoidalClosed.curry (λ_ X).hom := by
    rw [← unitIsoSelf_inv, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hk, MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry,
    leftUnitor_naturality]

theorem comp_toBidual_comp_pre_eq_curry' {M I : C} (s : 𝟙_ C ⟶ M) (ι : I ⟶ 𝟙_ C)
    (ψ : (ihom M).obj (𝟙_ C) ≅ I)
    (hψ : ψ.hom ≫ ι = (MonoidalClosed.pre s).app (𝟙_ C) ≫
      (MonoidalClosed.unitIsoSelf (𝟙_ C)).hom) :
    s ≫ toBidual M ≫ (MonoidalClosed.pre ψ.inv).app (𝟙_ C) = MonoidalClosed.curry' ι := by
  have hsev : s ▷ ((ihom M).obj (𝟙_ C)) ≫ (ihom.ev M).app (𝟙_ C) = (λ_ _).hom ≫ ψ.hom ≫ ι := by
    rw [show s ▷ ((ihom M).obj (𝟙_ C)) ≫ (ihom.ev M).app (𝟙_ C) =
      MonoidalClosed.uncurry ((MonoidalClosed.pre s).app (𝟙_ C)) from
        (MonoidalClosed.uncurry_pre s (𝟙_ C)).symm]
    exact uncurry_eq_of_comp_unitIsoSelf_hom _ _ hψ.symm
  symm
  rw [MonoidalClosed.curry', MonoidalClosed.curry_eq_iff, MonoidalClosed.uncurry_natural_left,
    MonoidalClosed.uncurry_pre_app, toBidual, MonoidalClosed.uncurry_curry,
    whisker_exchange_assoc, braiding_naturality_right_assoc]
  calc (ρ_ I).hom ≫ ι = ψ.inv ▷ 𝟙_ C ≫ (ρ_ _).hom ≫ ψ.hom ≫ ι := by
        rw [rightUnitor_naturality_assoc, Iso.inv_hom_id_assoc]
    _ = ψ.inv ▷ 𝟙_ C ≫ (β_ _ _).hom ≫ (λ_ _).hom ≫ ψ.hom ≫ ι := by
        rw [← braiding_leftUnitor]; simp only [Category.assoc]
    _ = _ := by
        congr 2
        exact hsev.symm

end ZDIsoMC

end MC

open AlgebraicGeometry

namespace ZDIsoAssembly

variable {X : Scheme.{u}} {M : X.Modules}

theorem exists_iso_of_psi (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (I : X.IdealSheafData)
    (ψ : Scheme.Modules.dual M ≅ I.module) (hψ : ψ.hom ≫ I.moduleι = Scheme.Modules.sectionDual s) :
    ∃ e : M ≅ I.invModule, s ≫ e.hom = I.invModuleSection := by
  have h1 : IsIso (ZDIsoMC.toBidual M) := (hM.isIso_ev_app_and_isIso_curry_braiding_ev).2
  let e : M ⟶ I.invModule := ZDIsoMC.toBidual M ≫ (MonoidalClosed.pre ψ.inv).app (𝟙_ X.Modules)
  have h2 : IsIso ((MonoidalClosed.pre ψ.inv).app (𝟙_ X.Modules)) :=
    ⟨⟨(MonoidalClosed.pre ψ.hom).app (𝟙_ X.Modules), by
      rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.hom_inv_id, MonoidalClosed.pre_id]; rfl, by
      rw [← NatTrans.comp_app, ← MonoidalClosed.pre_map, Iso.inv_hom_id, MonoidalClosed.pre_id]; rfl⟩⟩
  haveI : IsIso e := IsIso.comp_isIso' h1 h2
  refine ⟨asIso e, ?_⟩
  change s ≫ ZDIsoMC.toBidual M ≫ (MonoidalClosed.pre ψ.inv).app (𝟙_ X.Modules) = MonoidalClosed.curry' I.moduleι
  exact ZDIsoMC.comp_toBidual_comp_pre_eq_curry' s I.moduleι ψ hψ

end ZDIsoAssembly

theorem solution
    {X : Scheme.{u}} {M : X.Modules} (hM : Scheme.Modules.IsInvertible M) (s : 𝟙_ X.Modules ⟶ M)
    (hZ : (Scheme.Modules.zeroSchemeIdeal s).IsInvertible) :
    ∃ e : M ≅ (Scheme.Modules.zeroSchemeIdeal s).invModule,
      s ≫ e.hom = (Scheme.Modules.zeroSchemeIdeal s).invModuleSection := by
  obtain ⟨ψ, hψ⟩ := hM.exists_dual_iso_module_zeroSchemeIdeal s hZ
  exact ZDIsoAssembly.exists_iso_of_psi hM s _ ψ hψ
