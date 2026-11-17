/-
NEW EDITION CANDIDATE 002 (H5 lane4 a940f2af, 2026-11-17, lead request 07:23Z). NOT a recovery: no recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections.lean
  Source sha256  : 1c2b39587ee08697134d4def2d4ed8f74c3e90b27235bb9705a7520bff16ec38
  Retrieved      : pinned read-only clone ~/flt-src (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 6 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 6 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * CANDIDATE 005 drift-adaptation (tools/drift_rules_v2.py, the rule set compiled-proven in the NOS-core probe loop), applied: T6×1
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

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections
r2nos_namespace_dual

universe u

w03_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections.AlgebraicGeometry"

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Scheme Scheme.Modules Scheme.Modules.sheafify Scheme.Modules.tensorSections"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "ringCatSheaf Γ Modules Opens PresheafOfModules Modules.sheafify Modules.tensorSections"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "tensor sheafify tensorIsoSheafify tensorSections"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace SheafifyMu
r2nos_namespace_dual

w03_open "CategoryTheory CategoryTheory.MonoidalCategory Opposite TensorProduct"

variable {X : Scheme.{u}}

abbrev adj (X : Scheme.{u}) := SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

abbrev ι (X : Scheme.{u}) := SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

variable (L M : X.Modules)

def sheafifyTensorIso : (Modules.sheafify X).obj ((ι X).obj L ⊗ (ι X).obj M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify X) ((ι X).obj L) ((ι X).obj M)).symm ≪≫
    ((asIso (adj X).counit).app L ⊗ᵢ (asIso (adj X).counit).app M)

variable {L M}

lemma tensorSections_eq {U : X.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    Modules.tensorSections s t = (sheafifyTensorIso L M).hom.val.app (op U)
      (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
        ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))) := rfl

lemma sheafify_map_val_app_unit {P P' : X.PresheafOfModules} (g : P ⟶ P') (V : (X.Opens)ᵒᵖ) (z : P.obj V) :
    (((Modules.sheafify X).map g).val.app V) (((adj X).unit.app P).app V z) =
      ((adj X).unit.app P').app V (g.app V z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app V z) :)

lemma map_tensorHom_unit_comp (P Q : X.PresheafOfModules) :
    (Modules.sheafify X).map ((adj X).unit.app P ⊗ₘ (adj X).unit.app Q) ≫
      (sheafifyTensorIso ((Modules.sheafify X).obj P) ((Modules.sheafify X).obj Q)).hom ≫
        Functor.LaxMonoidal.μ (Modules.sheafify X) P Q = 𝟙 _ := by
  have hP : (Modules.sheafify X).map ((adj X).unit.app P) ≫ (adj X).counit.app ((Modules.sheafify X).obj P) =
      𝟙 _ := (adj X).left_triangle_components P
  have hQ : (Modules.sheafify X).map ((adj X).unit.app Q) ≫ (adj X).counit.app ((Modules.sheafify X).obj Q) =
      𝟙 _ := (adj X).left_triangle_components Q
  dsimp only [sheafifyTensorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom,
    MonoidalCategory.tensorIso_hom]
  rw [Functor.Monoidal.μIso_inv]
  simp only [← Category.assoc]
  erw [← Functor.OplaxMonoidal.δ_natural (Modules.sheafify X) ((adj X).unit.app P) ((adj X).unit.app Q)]
  rw [Category.assoc (Functor.OplaxMonoidal.δ (Modules.sheafify X) _ _)]
  erw [MonoidalCategory.tensorHom_comp_tensorHom, hP, hQ]
  erw [MonoidalCategory.id_tensorHom_id, Category.comp_id]
  exact Functor.Monoidal.δ_μ _ _ _

theorem sheafify_μ_app_tensorSections (P Q : X.PresheafOfModules) {U : X.Opens}
    (x : P.obj (op U)) (y : Q.obj (op U)) :
    (Functor.LaxMonoidal.μ (Modules.sheafify X) P Q).app U
      (Modules.tensorSections (L := (Modules.sheafify X).obj P) (M := (Modules.sheafify X).obj Q)
        (((adj X).unit.app P).app (op U) x) (((adj X).unit.app Q).app (op U) y)) =
    ((adj X).unit.app (P ⊗ Q)).app (op U) (x ⊗ₜ[Γ(X, U)] y) := by

  have H := congr($(map_tensorHom_unit_comp P Q).val.app (op U)
    (((adj X).unit.app (P ⊗ Q)).app (op U) (x ⊗ₜ[Γ(X, U)] y)))

  have h1 := (sheafify_map_val_app_unit ((adj X).unit.app P ⊗ₘ (adj X).unit.app Q) (op U)
      (x ⊗ₜ[Γ(X, U)] y)).trans
    (congrArg (((adj X).unit.app ((ι X).obj ((Modules.sheafify X).obj P) ⊗
        (ι X).obj ((Modules.sheafify X).obj Q))).app (op U))
      (ModuleCat.MonoidalCategory.tensorHom_tmul (((adj X).unit.app P).app (op U))
        (((adj X).unit.app Q).app (op U)) x y))
  exact (congrArg (fun z => (Functor.LaxMonoidal.μ (Modules.sheafify X) P Q).val.app (op U)
    ((sheafifyTensorIso ((Modules.sheafify X).obj P) ((Modules.sheafify X).obj Q)).hom.val.app (op U) z))
      h1).symm.trans H

end SheafifyMu

end AlgebraicGeometry.Scheme.Modules

end

open CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections.AlgebraicGeometry.Scheme.Modules TensorProduct _root_.TensorProduct in
r2nos_open_dual "CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections.AlgebraicGeometry.Scheme.Modules TensorProduct" in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} (P Q : X.PresheafOfModules) {U : X.Opens}
    (x : P.obj (Opposite.op U)) (y : Q.obj (Opposite.op U)) :
    (Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.sheafify X) P Q).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections
        (L := (AlgebraicGeometry.Scheme.Modules.sheafify X).obj P)
        (M := (AlgebraicGeometry.Scheme.Modules.sheafify X).obj Q)
        (((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app P).app (Opposite.op U) x)
        (((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app Q).app (Opposite.op U) y)) =
    ((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (P ⊗ Q)).app (Opposite.op U)
      (x ⊗ₜ[Γ(X, U)] y) :=
  SheafifyMu.sheafify_μ_app_tensorSections P Q x y
end S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
