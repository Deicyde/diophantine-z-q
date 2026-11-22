/-
NOS-CORE PROBE STAGING COPY (lane C4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_CategoryTheory_MonoidalClosed_isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit.lean
  Source sha256  : cc90475c94b52cfd3e9e9c6507b0c70ca99893868e9c3ad8f6f17f253d348298
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.CategoryTheory.Monoidal.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_CategoryTheory_MonoidalClosed_isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit
r2nos_namespace_dual

set_option autoImplicit false

universe v u

w03_open "CategoryTheory CategoryTheory.MonoidalCategory"

namespace ReflSol
r2nos_namespace_dual

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

set_option backward.defeqAttrib.useBackward true in
noncomputable def tensorLeftEquiv {M N : C} (e : M ⊗ N ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorLeft M) (tensorLeft N)
    (NatIso.ofComponents
      (fun X => (λ_ X).symm ≪≫ (whiskerRightIso ((β_ N M) ≪≫ e).symm X) ≪≫ α_ N M X)
      (by
        intro X Y f
        dsimp
        simp only [Category.assoc]
        rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, associator_naturality_right]))
    (NatIso.ofComponents
      (fun X => (α_ M N X).symm ≪≫ whiskerRightIso e X ≪≫ λ_ X)
      (by
        intro X Y f
        dsimp
        simp only [Category.assoc]
        rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc, leftUnitor_naturality]))

set_option backward.defeqAttrib.useBackward true in
noncomputable def tensorRightEquiv {M N : C} (e : M ⊗ N ≅ 𝟙_ C) : C ≌ C :=
  CategoryTheory.Equivalence.mk (tensorRight N) (tensorRight M)
    (NatIso.ofComponents
      (fun X => (ρ_ X).symm ≪≫ (whiskerLeftIso X ((β_ N M) ≪≫ e).symm) ≪≫ (α_ X N M).symm)
      (by
        intro X Y f
        dsimp
        simp only [Category.assoc]
        rw [rightUnitor_inv_naturality_assoc, ← whisker_exchange_assoc, associator_inv_naturality_left]))
    (NatIso.ofComponents
      (fun X => α_ X M N ≪≫ whiskerLeftIso X e ≪≫ ρ_ X)
      (by
        intro X Y f
        dsimp
        simp only [Category.assoc]
        rw [associator_naturality_left_assoc, ← whisker_exchange_assoc, rightUnitor_naturality]))

noncomputable def tensorLeftAdj {M N : C} (e : M ⊗ N ≅ 𝟙_ C) : tensorLeft M ⊣ tensorLeft N :=
  (tensorLeftEquiv e).toAdjunction

theorem isIso_tensorLeftAdj_counit_app {M N : C} (e : M ⊗ N ≅ 𝟙_ C) (X : C) :
    IsIso ((tensorLeftAdj e).counit.app X) := by
  change IsIso ((tensorLeftEquiv e).counitIso.hom.app X)
  infer_instance

noncomputable def tensorRightFF {M N : C} (e : M ⊗ N ≅ 𝟙_ C) : (tensorRight N).FullyFaithful :=
  (tensorRightEquiv e).fullyFaithfulFunctor

variable [MonoidalClosed C]

theorem isIso_ev_app {M N : C} (e : M ⊗ N ≅ 𝟙_ C) (X : C) : IsIso ((ihom.ev M).app X) := by
  have h := Adjunction.rightAdjointUniq_hom_app_counit (ihom.adjunction M) (tensorLeftAdj e) X

  have h' : (ihom.ev M).app X =
      (tensorLeft M).map (((ihom.adjunction M).rightAdjointUniq (tensorLeftAdj e)).hom.app X) ≫
        (tensorLeftAdj e).counit.app X := by
    rw [h]; rfl
  rw [h']
  haveI h1 : IsIso (((ihom.adjunction M).rightAdjointUniq (tensorLeftAdj e)).hom.app X) := inferInstance
  have h2 : IsIso ((tensorLeft M).map (((ihom.adjunction M).rightAdjointUniq (tensorLeftAdj e)).hom.app X)) :=
    Functor.map_isIso _ _
  exact IsIso.comp_isIso' h2 (isIso_tensorLeftAdj_counit_app e X)

theorem isIso_toBidual {M N : C} (e : M ⊗ N ≅ 𝟙_ C) :
    IsIso (MonoidalClosed.curry ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C))) := by

  let e' : M ⊗ (ihom M).obj (𝟙_ C) ≅ 𝟙_ C := @asIso _ _ _ _ ((ihom.ev M).app (𝟙_ C)) (isIso_ev_app e (𝟙_ C))
  have he' : e'.hom = (ihom.ev M).app (𝟙_ C) := rfl
  apply isIso_of_yoneda_map_bijective
  intro T
  have key : ∀ g : T ⟶ M,
      MonoidalClosed.uncurry (g ≫ MonoidalClosed.curry ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C)))
        = (β_ ((ihom M).obj (𝟙_ C)) T).hom ≫ ((g ▷ (ihom M).obj (𝟙_ C)) ≫ e'.hom) := by
    intro g
    rw [MonoidalClosed.uncurry_natural_left, MonoidalClosed.uncurry_curry, he',
      BraidedCategory.braiding_naturality_right_assoc]
  let Φ : (T ⟶ M) ≃ ((ihom M).obj (𝟙_ C) ⊗ T ⟶ 𝟙_ C) :=
    ((tensorRightFF e').homEquiv.trans (Iso.homCongr (Iso.refl _) e')).trans
      (Iso.homCongr (β_ ((ihom M).obj (𝟙_ C)) T).symm (Iso.refl _))
  have hΦ : ∀ g : T ⟶ M, Φ g = MonoidalClosed.uncurry
      (g ≫ MonoidalClosed.curry ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C))) := by
    intro g
    rw [key]
    simp [Φ, Iso.homCongr, Functor.FullyFaithful.homEquiv]
  have hfun : (fun g : T ⟶ M =>
        g ≫ MonoidalClosed.curry ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C)))
      = fun g => MonoidalClosed.curry (Φ g) := by
    funext g
    exact ((MonoidalClosed.curry_eq_iff _ _).mpr (hΦ g)).symm
  rw [hfun]
  exact (Φ.trans ⟨MonoidalClosed.curry, MonoidalClosed.uncurry, MonoidalClosed.uncurry_curry,
    MonoidalClosed.curry_uncurry⟩).bijective

end ReflSol

theorem solution
    {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C] [MonoidalClosed C]
    {M N : C} (e : M ⊗ N ≅ 𝟙_ C) :
    (∀ X : C, IsIso ((ihom.ev M).app X)) ∧
      IsIso (MonoidalClosed.curry
        ((β_ ((ihom M).obj (𝟙_ C)) M).hom ≫ (ihom.ev M).app (𝟙_ C))) :=
  ⟨ReflSol.isIso_ev_app e, ReflSol.isIso_toBidual e⟩
end S_CategoryTheory_MonoidalClosed_isIso_ev_app_and_isIso_curry_braiding_ev_of_tensor_iso_unit
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
