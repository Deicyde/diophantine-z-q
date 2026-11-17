/-
NEW EDITION CANDIDATE 002 (H5 lane4 a940f2af, 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.lean
  Source sha256  : dd302071b30517f2f7ee90bb870aeb2a559b62a25549dd6af6dbb3384658b8fc
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 2 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 6 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_InternalHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
r2nos_namespace_dual

universe u

w03_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.AlgebraicGeometry"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme.Modules.pullback Scheme.Hom Scheme.Opens.ι_appIso Scheme.Hom.image_preimage_eq_opensRange_inf Scheme Scheme.Modules Scheme.Opens Scheme.Modules.map_smul Scheme.Opens.opensRange_ι Scheme.Modules.IsFrameOn"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "forget ringCatSheaf Modules.pullback Hom Γ Opens.ι_appIso Hom.image_preimage_eq_opensRange_inf Modules.restrictFunctor Modules.restrictFunctorIsoPullback restrictFunctor Modules Opens grothendieckTopology Modules.map_smul Opens.opensRange_ι restrict PresheafOfModules Modules.IsFrameOn"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "hom_ext toPresheaf pushforward pullback presheaf Hom restrictFunctor restrictFunctorIsoPullback restrict map_smul IsFrameOn"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace FrameBridge
r2nos_namespace_dual

open Opposite TopologicalSpace
r2nos_open_dual "Opposite TopologicalSpace"

variable {X : Scheme.{u}}

section restrict

variable (W : X.Opens)

def restrictRingCatSheafHom : (W : Scheme.{u}).ringCatSheaf ⟶
    (W.ι.opensFunctor.sheafPushforwardContinuous RingCat.{u}
      (Opens.grothendieckTopology (W : Scheme.{u})) (Opens.grothendieckTopology X)).obj
        X.ringCatSheaf :=
  ⟨𝟙 _⟩

def restrictFunctor' : X.Modules ⥤ (W : Scheme.{u}).Modules :=
  SheafOfModules.pushforward (restrictRingCatSheafHom W)

lemma restrictFunctor'_eq : restrictFunctor' W = Modules.restrictFunctor W.ι := by
  dsimp only [restrictFunctor', Modules.restrictFunctor, restrictRingCatSheafHom]
  congr 2
  ext V : 2
  change 𝟙 _ = (forget₂ CommRingCat RingCat).map (W.ι.appIso V.unop).inv
  rw [Scheme.Opens.ι_appIso]
  rfl

def restrictFunctor'IsoPullback : restrictFunctor' W ≅ Modules.pullback W.ι :=
  eqToIso (restrictFunctor'_eq W) ≪≫ Modules.restrictFunctorIsoPullback W.ι

lemma image_le (W' : (W : Scheme.{u}).Opens) : W.ι ''ᵁ W' ≤ W :=
  (W.ι.image_le_opensRange W').trans_eq W.opensRange_ι

variable {W} in
lemma image_preimage_of_le {W₂ : X.Opens} (h : W₂ ≤ W) : W.ι ''ᵁ (W.ι ⁻¹ᵁ W₂) = W₂ := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

abbrev secX (W' : (W : Scheme.{u}).Opens) (a : Γ(W, W')) : Γ(X, W.ι ''ᵁ W') := a

end restrict

section smulHom

variable (N : X.Modules) (W : X.Opens) (τ : Γ(N, W))

def smulSectionHom : SheafOfModules.unit ((W : X.Opens) : Scheme.{u}).ringCatSheaf ⟶
    (restrictFunctor' W).obj N :=
  ⟨{ app := fun W' => ModuleCat.ofHom
      { toFun := fun a =>
          (secX W W'.unop a • N.presheaf.map (homOfLE (image_le W W'.unop)).op τ : Γ(N, W.ι ''ᵁ W'.unop))
        map_add' := fun a b => add_smul (secX W W'.unop a) (secX W W'.unop b) _
        map_smul' := fun r a => mul_smul (secX W W'.unop r) (secX W W'.unop a) _ }
     naturality := fun {W' W''} i => by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro a
       show secX W W''.unop (X.presheaf.map (W.ι.opensFunctor.map i.unop).op (secX W W'.unop a)) •
           N.presheaf.map (homOfLE (image_le W W''.unop)).op τ =
         N.presheaf.map (W.ι.opensFunctor.map i.unop).op
           (secX W W'.unop a • N.presheaf.map (homOfLE (image_le W W'.unop)).op τ)
       rw [Scheme.Modules.map_smul]
       congr 1
       change _ = (N.presheaf.map _ ≫ N.presheaf.map _) τ
       rw [← N.presheaf.map_comp]
       rfl }⟩

lemma smulSectionHom_app_apply (W' : (((W : X.Opens) : Scheme.{u}).Opens)ᵒᵖ) (a : Γ(W, W'.unop)) :
    (smulSectionHom N W τ).val.app W' a =
      secX W W'.unop a • N.presheaf.map (homOfLE (image_le W W'.unop)).op τ := rfl

variable {N W τ}

lemma isIso_smulSectionHom_of_bijective
    (hb : ∀ W' : (((W : X.Opens) : Scheme.{u}).Opens)ᵒᵖ, Function.Bijective ((smulSectionHom N W τ).val.app W')) :
    IsIso (smulSectionHom N W τ) := by
  set ψ := smulSectionHom N W τ
  have h₂ : IsIso ((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map ψ)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro W'
    have : IsIso ((CategoryTheory.forget Ab).map
        (((PresheafOfModules.toPresheaf _).map ((SheafOfModules.forget _).map ψ)).app W')) :=
      (isIso_iff_bijective _).2 (hb W')
    exact isIso_of_reflects_iso _ (CategoryTheory.forget Ab)
  have := (SheafOfModules.fullyFaithfulForget (((W : X.Opens) : Scheme.{u}).ringCatSheaf)).reflectsIsomorphisms
  have h₃ := isIso_of_reflects_iso ((SheafOfModules.forget _).map ψ) (PresheafOfModules.toPresheaf _)
  exact isIso_of_reflects_iso ψ (SheafOfModules.forget _)

end smulHom

variable {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)}

theorem isIso_smulSectionHom (h : IsFrameOn s V) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) :
    IsIso (smulSectionHom M W (M.presheaf.map (homOfLE hWU).op s)) := by
  apply isIso_smulSectionHom_of_bijective
  intro W'
  have e : M.presheaf.map (homOfLE (image_le W W'.unop)).op (M.presheaf.map (homOfLE hWU).op s) =
      M.presheaf.map (homOfLE ((image_le W W'.unop).trans hWU)).op s := by
    change (M.presheaf.map _ ≫ M.presheaf.map _) s = _
    rw [← M.presheaf.map_comp]
    rfl
  have hb := h ((image_le W W'.unop).trans hWU) ((image_le W W'.unop).trans hWV)
  rw [← e] at hb
  exact hb

theorem nonempty_pullback_iso_unit (h : IsFrameOn s V) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) :
    Nonempty ((Scheme.Modules.pullback W.ι).obj M ≅ SheafOfModules.unit (W : Scheme.{u}).ringCatSheaf) :=
  haveI := isIso_smulSectionHom h W hWU hWV
  ⟨((restrictFunctor'IsoPullback W).symm.app M) ≪≫
    (asIso (smulSectionHom M W (M.presheaf.map (homOfLE hWU).op s))).symm⟩

end FrameBridge

end AlgebraicGeometry.Scheme.Modules

end

open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.AlgebraicGeometry.Scheme.Modules in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit.AlgebraicGeometry.Scheme.Modules" in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {U V : X.Opens} {s : Γ(M, U)}
    (h : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (W : X.Opens) (hWU : W ≤ U) (hWV : W ≤ V) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj M ≅
      SheafOfModules.unit (W : AlgebraicGeometry.Scheme.{u}).ringCatSheaf) :=
  FrameBridge.nonempty_pullback_iso_unit h W hWU hWV
end S_AlgebraicGeometry_Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
