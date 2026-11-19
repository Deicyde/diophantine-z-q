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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections.lean
  Source sha256  : fd1801dee5cb084a92861357117f26925bb3c820ff39b7cf3ebf67b105928943
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
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
  * lane C4 hand repair (2026-11-17; SOURCE ONLY, UNCOMPILED, pending C6 review):
    in `unitTensorIso_hom_comp_leftUnitor_hom` the step `rw [MonoidalCategory.tensorIso_hom, Iso.app_hom,
    asIso_hom, Iso.symm_hom]` is dropped: at Mathlib 56a0058 the preceding `dsimp only [...]` already
    performs these rewrites (`tensorIso` is `@[simps]`), so the pattern `(?f ⊗ᵢ ?g).hom` no longer occurs.
    No statement, declaration, import or option changed.
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

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections
r2nos_namespace_dual

universe u

w03_open "CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections.AlgebraicGeometry"

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
w03_export "AlgebraicGeometry.Scheme.Modules" "sheafify tensorSections"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace UnitorSections
r2nos_namespace_dual

open Opposite TensorProduct
r2nos_open_dual "Opposite TensorProduct"

variable {X : Scheme.{u}}

abbrev adj (X : Scheme.{u}) := SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

abbrev ι (X : Scheme.{u}) := SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

lemma sheafify_map_val_app_unit {P P' : X.PresheafOfModules} (g : P ⟶ P') (V : (X.Opens)ᵒᵖ) (z : P.obj V) :
    (((Modules.sheafify X).map g).val.app V) (((adj X).unit.app P).app V z) =
      ((adj X).unit.app P').app V (g.app V z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app V z) :)

lemma counit_val_app_unit (N : X.Modules) (V : (X.Opens)ᵒᵖ) (y : N.val.obj V) :
    (((adj X).counit.app N).val.app V) (((adj X).unit.app ((ι X).obj N)).app V y) = y := by
  have h := (adj X).right_triangle_components N
  exact (congr($(h).app V y) :)

variable (N : X.Modules)

def unitTensorIso : (Modules.sheafify X).obj (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N) ≅ 𝟙_ X.Modules ⊗ N :=
  (Functor.Monoidal.μIso (Modules.sheafify X) (𝟙_ X.PresheafOfModules) ((ι X).obj N)).symm ≪≫
    ((Functor.Monoidal.εIso (Modules.sheafify X)).symm ⊗ᵢ (asIso (adj X).counit).app N)

lemma unitTensorIso_hom_comp_leftUnitor_hom :
    (unitTensorIso N).hom ≫ (λ_ N).hom =
      (Modules.sheafify X).map (λ_ ((ι X).obj N)).hom ≫ (adj X).counit.app N := by
  dsimp only [unitTensorIso, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, asIso_hom,
    MonoidalCategory.tensorIso_hom, Iso.symm_inv]
  rw [Functor.Monoidal.μIso_inv, Functor.Monoidal.εIso_inv, Functor.Monoidal.map_leftUnitor,
    MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  erw [← MonoidalCategory.leftUnitor_naturality ((adj X).counit.app N)]
  all_goals rfl

theorem leftUnitor_hom_app_tensorSections {U : X.Opens} (g : Γ(X, U)) (n : Γ(N, U)) :
    (λ_ N).hom.app U (Modules.tensorSections (L := 𝟙_ X.Modules) (M := N) g n) = g • n := by
  have h := congr($(unitTensorIso_hom_comp_leftUnitor_hom N).val.app (op U)
    (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N)).app (op U)
      ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U)))))
  have h' : (λ_ N).hom.val.app (op U) ((unitTensorIso N).hom.val.app (op U)
      (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N)).app (op U)
        ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U))))) =
      ((adj X).counit.app N).val.app (op U) (((Modules.sheafify X).map (λ_ ((ι X).obj N)).hom).val.app (op U)
        (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N)).app (op U)
          ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U))))) := h
  change (λ_ N).hom.val.app (op U) ((unitTensorIso N).hom.val.app (op U)
      (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N)).app (op U)
        ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U))))) = g • n
  rw [h']
  letI : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))

  exact (congrArg (((adj X).counit.app N).val.app (op U))
      (sheafify_map_val_app_unit (λ_ ((ι X).obj N)).hom (op U) _)).trans
    ((counit_val_app_unit N (op U) _).trans (ModuleCat.MonoidalCategory.leftUnitor_hom_apply _ _))

end UnitorSections

end AlgebraicGeometry.Scheme.Modules

end

open CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections.AlgebraicGeometry.Scheme.Modules in
r2nos_open_dual "CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections.AlgebraicGeometry.Scheme.Modules" in

theorem solution {X : AlgebraicGeometry.Scheme.{u}} {N : X.Modules} {U : X.Opens} (g : Γ(X, U)) (n : Γ(N, U)) :
    (λ_ N).hom.app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (L := 𝟙_ X.Modules) (M := N) g n) = g • n :=
  UnitorSections.leftUnitor_hom_app_tensorSections N g n
end S_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
