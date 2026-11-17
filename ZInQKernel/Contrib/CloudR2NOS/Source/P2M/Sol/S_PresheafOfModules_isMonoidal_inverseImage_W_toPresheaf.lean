/-
NEW EDITION CANDIDATE 002 (H5 lane4 , 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.lean
  Source sha256  : 9f8d9eb5c6394a82092a1a5289d8fd33807d4f5aabe29ad34e9954e921d48538
  Retrieved      : pinned read-only clone the upstream FLT repository (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 7 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * CANDIDATE 005 drift-adaptation (tools/drift_rules_v2.py, the rule set compiled-proven in the NOS-core probe loop), applied: R2×1
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_InternalHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_PresheafOfModules_isSheaf_ihomObj
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits CategoryTheory.MonoidalCategory.Limits"

noncomputable section

namespace PresheafOfModules
r2nos_namespace_dual
w03_export "PresheafOfModules" "sheafification presheaf sheafificationAdjunction inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms map restrictScalars IsLocallyInjective toPresheaf unit toPresheaf_map_sheafificationAdjunction_unit_app obj IsLocallySurjective isSheaf_ihomObj"
namespace IsMonoidalW
r2nos_namespace_dual
w03_open "PresheafOfModules"

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Sheaf J RingCat.{u})
  (α : 𝒪 ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

abbrev PMod := PresheafOfModules.{u} (𝒪 ⋙ forget₂ CommRingCat RingCat)

private abbrev _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.PresheafOfModules.IsMonoidalW.W : MorphismProperty (PMod 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))

w03_export "PresheafOfModules.IsMonoidalW" "W"

abbrev shf : PMod 𝒪 ⥤ SheafOfModules.{u} R := PresheafOfModules.sheafification α

abbrev inc : SheafOfModules.{u} R ⥤ PMod 𝒪 :=
  SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α

abbrev adj : shf 𝒪 R α ⊣ inc 𝒪 R α := PresheafOfModules.sheafificationAdjunction α

scoped instance : (inc 𝒪 R α).Faithful := (adj 𝒪 R α).fullyFaithfulROfIsIsoCounit.faithful
scoped instance : (inc 𝒪 R α).Full := (adj 𝒪 R α).fullyFaithfulROfIsIsoCounit.full

lemma W_eq : W (J := J) 𝒪 = (MorphismProperty.isomorphisms _).inverseImage (shf 𝒪 R α) :=
  PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms α

lemma isIso_unit_app_of_isSheaf (N : PMod 𝒪) (hN : Presheaf.IsSheaf J N.presheaf) :
    IsIso ((adj 𝒪 R α).unit.app N) := by
  have : IsIso ((PresheafOfModules.toPresheaf _).map ((adj 𝒪 R α).unit.app N)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact isIso_toSheafify J hN
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)

lemma isIso_shf_map_unit_whiskerRight (d d' : PMod 𝒪) :
    IsIso ((shf 𝒪 R α).map (((adj 𝒪 R α).unit.app d) ▷ d')) := by
  have h := (Monoidal.Reflective.isIso_tfae (adj 𝒪 R α)).out 1 3
  refine (h.mp ?_) d d'
  intro c d
  apply isIso_unit_app_of_isSheaf
  exact PresheafOfModules.isSheaf_ihomObj _ _ c.isSheaf

include R α in
lemma W_whiskerRight {d₁ d₂ : PMod 𝒪} (g : d₁ ⟶ d₂) (hg : W (J := J) 𝒪 g) (d' : PMod 𝒪) :
    W (J := J) 𝒪 (g ▷ d') := by
  have two3 : (W (J := J) 𝒪).HasTwoOutOfThreeProperty := by
    rw [W_eq 𝒪 R α]; infer_instance
  have hη : ∀ d : PMod 𝒪, W (J := J) 𝒪 ((adj 𝒪 R α).unit.app d ▷ d') := fun d => by
    rw [W_eq 𝒪 R α]
    exact isIso_shf_map_unit_whiskerRight 𝒪 R α d d'
  have hiso : W (J := J) 𝒪 ((inc 𝒪 R α).map ((shf 𝒪 R α).map g) ▷ d') := by
    rw [W_eq 𝒪 R α] at hg ⊢
    simp only [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff] at hg ⊢
    have : IsIso ((inc 𝒪 R α).map ((shf 𝒪 R α).map g)) := Functor.map_isIso _ _
    infer_instance
  have e := (adj 𝒪 R α).unit_naturality g
  have hη₁ := hη d₁
  have hη₂ := hη d₂

  dsimp only [Functor.comp_obj, Functor.id_obj] at e hη₁ hη₂ hiso ⊢
  have h' := (W (J := J) 𝒪).comp_mem _ _ hη₁ hiso
  rw [← comp_whiskerRight, e, comp_whiskerRight] at h'
  exact (W (J := J) 𝒪).of_postcomp _ _ hη₂ h'

end PresheafOfModules.IsMonoidalW
w03_reactivate "P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.PresheafOfModules P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.PresheafOfModules.IsMonoidalW"
w03_reactivate "P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.PresheafOfModules"

end
w03_reactivate "P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.PresheafOfModules P2MW.S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.PresheafOfModules.IsMonoidalW"

open PresheafOfModules.IsMonoidalW in
r2nos_open_dual "PresheafOfModules.IsMonoidalW" in

theorem solution {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Sheaf J RingCat.{u})
    (α : 𝒪 ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] :
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))).IsMonoidal where
  whiskerRight g hg d' := W_whiskerRight 𝒪 R α g hg d'
  whiskerLeft d g₁ g₂ g hg :=
    ((W (J := J) 𝒪).arrow_mk_iso_iff (Arrow.isoMk' (g ▷ d) (d ◁ g) (β_ g₁ d) (β_ g₂ d)
      (BraidedCategory.braiding_naturality_left g d).symm)).1 (W_whiskerRight 𝒪 R α g hg d)
end S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
