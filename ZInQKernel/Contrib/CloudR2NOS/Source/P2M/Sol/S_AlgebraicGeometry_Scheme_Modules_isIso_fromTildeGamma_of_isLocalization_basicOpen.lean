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
  Source file    : P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen.lean
  Source sha256  : 8fdd79a1c875f4e1989287f5464b75bad2cc75325ebaaeea91f03ba67f6a30e6
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 5 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 5 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 2 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib.AlgebraicGeometry.Modules.Tilde
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_iff_isLocalizedModule
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen
r2nos_namespace_dual

set_option autoImplicit false

universe u

w03_open "CategoryTheory AlgebraicGeometry P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen.AlgebraicGeometry Opposite TopologicalSpace"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Spec Scheme tilde.isUnit_algebraMap_end_basicOpen modulesSpecToSheaf StructureSheaf.globalSectionsIso Scheme.Modules tilde basicOpen_eq_of_affine Scheme.ΓSpecIso Scheme.Modules.isIso_fromTildeGamma_iff_isLocalizedModule"
namespace Scheme
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme" "mk Γ basicOpen Modules Opens basicOpen_le ΓSpecIso Modules.isIso_fromTildeGamma_iff_isLocalizedModule"
namespace Modules
r2nos_namespace_dual
w03_export "AlgebraicGeometry.Scheme.Modules" "presheaf fromTildeΓ isIso_fromTildeGamma_iff_isLocalizedModule"
w03_open "AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme AlgebraicGeometry"

namespace TildeOfLoc
r2nos_namespace_dual

variable {R : CommRingCat.{u}} (M : (Spec (.of R)).Modules)

noncomputable abbrev Γ' (W : (Spec (.of R)).Opens) : ModuleCat R := (modulesSpecToSheaf.obj M).1.obj (op W)

noncomputable abbrev res' (W : (Spec (.of R)).Opens) : Γ' M ⊤ →ₗ[R] Γ' M W :=
  ((modulesSpecToSheaf.obj M).1.map (homOfLE (le_top : W ≤ ⊤)).op).hom

theorem res'_apply (W : (Spec (.of R)).Opens) (y : Γ(M, ⊤)) :
    res' M W y = (M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op) y := rfl

theorem smul_def (W : (Spec (.of R)).Opens) (r : R) (m : Γ' M W) :
    r • m = (((Spec (.of R)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
      ((StructureSheaf.globalSectionsIso R).hom.hom r)) • (show Γ(M, W) from m) := rfl

omit M in
theorem globalSectionsIso_hom_apply (r : R) :
    (StructureSheaf.globalSectionsIso R).hom.hom r = (Scheme.ΓSpecIso (.of R)).inv.hom r := rfl

omit M in
theorem res_top_top (s : Γ(Spec (.of R), ⊤)) :
    ((Spec (.of R)).presheaf.map (homOfLE (le_top : (⊤ : (Spec (.of R)).Opens) ≤ ⊤)).op).hom s = s := by
  rw [Subsingleton.elim (homOfLE (le_top : (⊤ : (Spec (.of R)).Opens) ≤ ⊤)) (𝟙 _), op_id,
    CategoryTheory.Functor.map_id]
  rfl

def LocClauses (W : (Spec (.of R)).Opens) (g : Γ(Spec (.of R), ⊤)) : Prop :=
  (∀ x : Γ(M, W), ∃ (n : ℕ) (y : Γ(M, ⊤)),
      M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op y
        = ((Spec (.of R)).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom (g ^ n) • x)
    ∧ (∀ y : Γ(M, ⊤), M.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op y = 0 → ∃ n : ℕ, (g ^ n) • y = 0)

theorem isLocalizedModule_of_locClauses (f : R) (W : (Spec (.of R)).Opens)
    (hunit : IsUnit (algebraMap R (Module.End R (Γ' M W)) f))
    (h : LocClauses M W ((Scheme.ΓSpecIso (.of R)).inv.hom f)) :
    IsLocalizedModule (Submonoid.powers f) (res' M W) := by
  obtain ⟨h1, h2⟩ := h
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · rintro ⟨c, n, rfl⟩
    rw [map_pow]
    exact hunit.pow n
  · intro x
    obtain ⟨n, y, hy⟩ := h1 x
    refine ⟨(y, ⟨f ^ n, n, rfl⟩), ?_⟩
    show (f ^ n) • x = res' M W y
    rw [res'_apply, hy, smul_def, globalSectionsIso_hom_apply, map_pow]
  · intro y₁ y₂ hyy
    have h0 : res' M W (y₁ - y₂) = 0 := by
      rw [map_sub, sub_eq_zero]; exact hyy
    obtain ⟨n, hn⟩ := h2 (y₁ - y₂) h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    show (f ^ n) • y₁ = (f ^ n) • y₂
    rw [← sub_eq_zero, ← smul_sub, smul_def, globalSectionsIso_hom_apply, map_pow, res_top_top]
    exact hn

end TildeOfLoc

end AlgebraicGeometry.Scheme.Modules

open _root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen.AlgebraicGeometry.Scheme.Modules in
r2nos_open_dual "_root_.AlgebraicGeometry.Scheme.Modules _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen.AlgebraicGeometry.Scheme.Modules" in
theorem solution
    {R : CommRingCat.{u}} (M : (Spec (.of R)).Modules)
    (hloc : ∀ g : Γ(Spec (.of R), ⊤),
      (∀ x : Γ(M, (Spec (.of R)).basicOpen g), ∃ (n : ℕ) (y : Γ(M, ⊤)),
          M.presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op y
            = ((Spec (.of R)).presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op).hom (g ^ n) • x)
        ∧ (∀ y : Γ(M, ⊤), M.presheaf.map (homOfLE ((Spec (.of R)).basicOpen_le g)).op y = 0 →
            ∃ n : ℕ, (g ^ n) • y = 0)) :
    IsIso M.fromTildeΓ := by
  rw [AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_iff_isLocalizedModule]
  intro f
  have hW : (Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv.hom f) = PrimeSpectrum.basicOpen f :=
    basicOpen_eq_of_affine (R := .of R) f
  have h : TildeOfLoc.LocClauses M ((Spec (.of R)).basicOpen ((Scheme.ΓSpecIso (.of R)).inv.hom f))
      ((Scheme.ΓSpecIso (.of R)).inv.hom f) :=
    hloc _
  rw [hW] at h
  exact TildeOfLoc.isLocalizedModule_of_locClauses M f (PrimeSpectrum.basicOpen f)
    (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := M) f le_rfl) h
end S_AlgebraicGeometry_Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
