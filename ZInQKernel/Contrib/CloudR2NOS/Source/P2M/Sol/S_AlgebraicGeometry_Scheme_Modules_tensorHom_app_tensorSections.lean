/-
NEW EDITION CANDIDATE 002 (H5 lane4 , 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections.lean
  Source sha256  : ea523a5e1dfe409d6e1139d4fad391e7404e7313e1c7e969e4babf91bb2c77ea
  Retrieved      : pinned read-only clone the upstream FLT repository (6e837e75), byte-for-byte
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

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections
r2nos_namespace_dual

universe u

w03_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections.AlgebraicGeometry"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.tensorSections"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "ringCatSheaf Γ Modules Opens PresheafOfModules Modules.sheafify Modules.tensorSections"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "sheafify tensorIsoSheafify tensorSections"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace TensorHomSections
r2nos_namespace_dual

open Opposite TensorProduct
r2nos_open_dual "Opposite TensorProduct"

variable {X : Scheme.{u}} {L L' M M' : X.Modules}

abbrev adj (X : Scheme.{u}) := SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

abbrev ι (X : Scheme.{u}) := SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

variable (L M)

def sheafifyTensorIso : (Modules.sheafify X).obj ((ι X).obj L ⊗ (ι X).obj M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify X) ((ι X).obj L) ((ι X).obj M)).symm ≪≫
    ((asIso (adj X).counit).app L ⊗ᵢ (asIso (adj X).counit).app M)

variable {L M}

lemma sheafifyTensorIso_hom_naturality (f : L ⟶ L') (g : M ⟶ M') :
    (Modules.sheafify X).map ((ι X).map f ⊗ₘ (ι X).map g) ≫ (sheafifyTensorIso L' M').hom =
      (sheafifyTensorIso L M).hom ≫ (f ⊗ₘ g) := by
  dsimp only [sheafifyTensorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom,
    MonoidalCategory.tensorIso_hom]
  simp only [MonoidalCategory.tensorIso_hom, Iso.app_hom, asIso_hom]
  rw [Functor.Monoidal.μIso_inv, Functor.Monoidal.μIso_inv, ← Category.assoc,
    ← Functor.OplaxMonoidal.δ_natural, Category.assoc, Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, MonoidalCategory.tensorHom_comp_tensorHom]
  erw [(adj X).counit.naturality f, (adj X).counit.naturality g]
  rfl

lemma tensorSections_eq {U : X.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    Modules.tensorSections s t = (sheafifyTensorIso L M).hom.val.app (op U)
      (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
        ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))) := rfl

lemma sheafify_map_val_app_unit {P P' : X.PresheafOfModules} (g : P ⟶ P') (V : (X.Opens)ᵒᵖ) (z : P.obj V) :
    (((Modules.sheafify X).map g).val.app V) (((adj X).unit.app P).app V z) =
      ((adj X).unit.app P').app V (g.app V z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app V z) :)

theorem tensorHom_app_tensorSections (φ : L ⟶ L') (ψ : M ⟶ M') {U : X.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    (φ ⊗ₘ ψ).app U (Modules.tensorSections s t) = Modules.tensorSections (φ.app U s) (ψ.app U t) := by
  have h := congr($(sheafifyTensorIso_hom_naturality φ ψ).val.app (op U)
    (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
      ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))))

  have h' : (sheafifyTensorIso L' M').hom.val.app (op U)
      (((Modules.sheafify X).map ((ι X).map φ ⊗ₘ (ι X).map ψ)).val.app (op U)
        (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
          ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))))) =
      (φ ⊗ₘ ψ).val.app (op U) ((sheafifyTensorIso L M).hom.val.app (op U)
        (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
          ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))))) := h
  rw [tensorSections_eq, tensorSections_eq]
  change (φ ⊗ₘ ψ).val.app (op U) ((sheafifyTensorIso L M).hom.val.app (op U)
    (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
      ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))))) = _
  rw [← h']
  erw [sheafify_map_val_app_unit ((ι X).map φ ⊗ₘ (ι X).map ψ) (op U)]
  congr 1
  all_goals (erw [PresheafOfModules.Monoidal.tensorHom_app])
  all_goals exact ModuleCat.MonoidalCategory.tensorHom_tmul _ _ _ _

end TensorHomSections

end AlgebraicGeometry.Scheme.Modules

end

open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections.AlgebraicGeometry.Scheme.Modules in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections.AlgebraicGeometry.Scheme.Modules" in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {L L' M M' : X.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (φ ⊗ₘ ψ).app U (AlgebraicGeometry.Scheme.Modules.tensorSections s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (φ.app U s) (ψ.app U t) :=
  TensorHomSections.tensorHom_app_tensorSections φ ψ s t
end S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
