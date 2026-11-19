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
  Source file    : Definitions/Def_AlgebraicGeometry_TwoChartCechSectionsOf.lean
  Source sha256  : 6202464487ff940e1941a8d567212b8b06cb0067f5f6c637ac9dead730cc3470
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
r2nos_open_dual "CategoryTheory CategoryTheory.Limits Opposite"

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover
r2nos_namespace_dual

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

@[reducible] def moduleSectionsOfHom (c : X ⟶ Spec (.of R)) (M : X.Modules) (U : X.Opens) :
    Module R Γ(M, U) :=
  letI := algebraOfHom c U
  Module.compHom Γ(M, U) (algebraMap R Γ(X, U))

theorem isScalarTower_sections (c : X ⟶ Spec (.of R)) (M : X.Modules) (U : X.Opens) :
    letI := algebraOfHom c U; letI := moduleSectionsOfHom c M U
    IsScalarTower R Γ(X, U) Γ(M, U) :=
  letI := algebraOfHom c U; letI := moduleSectionsOfHom c M U
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

def restrictSections (c : X ⟶ Spec (.of R)) (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    letI := moduleSectionsOfHom c M U; letI := moduleSectionsOfHom c M V
    Γ(M, U) →ₗ[R] Γ(M, V) :=
  letI := algebraOfHom c U; letI := algebraOfHom c V
  letI := moduleSectionsOfHom c M U; letI := moduleSectionsOfHom c M V
  { toFun := fun x => M.presheaf.map (homOfLE h).op x
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => by
      show M.presheaf.map (homOfLE h).op ((algebraMap R Γ(X, U) r) • x)
        = (algebraMap R Γ(X, V) r) • M.presheaf.map (homOfLE h).op x
      rw [Scheme.Modules.map_smul]
      congr 1
      exact (restrictAlgHom c h).commutes r }

theorem restrictSections_apply (c : X ⟶ Spec (.of R)) (M : X.Modules) {U V : X.Opens} (h : V ≤ U) (x : Γ(M, U)) :
    letI := moduleSectionsOfHom c M U; letI := moduleSectionsOfHom c M V
    restrictSections c M h x = M.presheaf.map (homOfLE h).op x := rfl

variable (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) (M : X.Modules)

def sectionsOf : TwoChartCech.Sections (𝒱.cover c) :=
  letI : Module (𝒱.cover c).A0 Γ(M, 𝒱.U0) := inferInstanceAs (Module Γ(X, 𝒱.U0) Γ(M, 𝒱.U0))
  letI : Module (𝒱.cover c).A1 Γ(M, 𝒱.U1) := inferInstanceAs (Module Γ(X, 𝒱.U1) Γ(M, 𝒱.U1))
  letI : Module (𝒱.cover c).A01 Γ(M, 𝒱.U0 ⊓ 𝒱.U1) :=
    inferInstanceAs (Module Γ(X, 𝒱.U0 ⊓ 𝒱.U1) Γ(M, 𝒱.U0 ⊓ 𝒱.U1))
  letI : Module R Γ(M, 𝒱.U0) := moduleSectionsOfHom c M 𝒱.U0
  letI : Module R Γ(M, 𝒱.U1) := moduleSectionsOfHom c M 𝒱.U1
  letI : Module R Γ(M, 𝒱.U0 ⊓ 𝒱.U1) := moduleSectionsOfHom c M (𝒱.U0 ⊓ 𝒱.U1)
  haveI : IsScalarTower R (𝒱.cover c).A0 Γ(M, 𝒱.U0) := isScalarTower_sections c M 𝒱.U0
  haveI : IsScalarTower R (𝒱.cover c).A1 Γ(M, 𝒱.U1) := isScalarTower_sections c M 𝒱.U1
  haveI : IsScalarTower R (𝒱.cover c).A01 Γ(M, 𝒱.U0 ⊓ 𝒱.U1) := isScalarTower_sections c M (𝒱.U0 ⊓ 𝒱.U1)
  { M0 := Γ(M, 𝒱.U0)
    M1 := Γ(M, 𝒱.U1)
    M01 := Γ(M, 𝒱.U0 ⊓ 𝒱.U1)
    r0 := restrictSections c M inf_le_left
    r1 := restrictSections c M inf_le_right
    r0_smul := fun a m => by
      exact Scheme.Modules.map_smul M (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)) a m
    r1_smul := fun a m => by
      exact Scheme.Modules.map_smul M (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)) a m }

theorem sectionsOf_M0 : (𝒱.sectionsOf c M).M0 = Γ(M, 𝒱.U0) := rfl
theorem sectionsOf_M1 : (𝒱.sectionsOf c M).M1 = Γ(M, 𝒱.U1) := rfl
theorem sectionsOf_M01 : (𝒱.sectionsOf c M).M01 = Γ(M, 𝒱.U0 ⊓ 𝒱.U1) := rfl
theorem sectionsOf_r0_apply (x : Γ(M, 𝒱.U0)) :
    (𝒱.sectionsOf c M).r0 (show (𝒱.sectionsOf c M).M0 from x)
      = M.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op x := rfl
theorem sectionsOf_r1_apply (x : Γ(M, 𝒱.U1)) :
    (𝒱.sectionsOf c M).r1 (show (𝒱.sectionsOf c M).M1 from x)
      = M.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op x := rfl

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
