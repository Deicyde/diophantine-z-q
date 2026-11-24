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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left.lean
  Source sha256  : fbad8cbbe5de82d21da975155c883cfcdb6a3293aa2a3737af067cfbd3e1a9dd
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `_root_.` reference(s)/declaration head(s) to source-specific names qualified with `ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * REMOVED source option(s) (default-options rule): `set_option linter.unusedSectionVars false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 5 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
  * DRIFT/PORT-PITFALL RULES v1 (lane C4 drift rules v1), applied: T7×2; rule citations in the batch ledger.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_comp_d
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_Module_Finite_of_ker_le_range_of_isNoetherianRing
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left
r2nos_namespace_dual

set_option autoImplicit false

w03_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left.AlgebraicGeometry CategoryTheory"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Surjective Spec Scheme IsSeparated IsNoetherian OModulePresheaf.AffSES OModulePresheaf"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "AffHom AffSES AffHom.cochainMap cochain d H0 CechFinite d_comp_d"
namespace LES
r2nos_namespace_dual
w03_open "AlgebraicGeometry.OModulePresheaf AlgebraicGeometry"

universe u

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
variable (K : V.OrderedAffineCover) {F₁ F₂ F₃ : OModulePresheaf π} (S : AffSES F₁ F₂ F₃)

local notation "ιC" => AffHom.cochainMap (π := π) K S.inc
local notation "πC" => AffHom.cochainMap (π := π) K S.proj

theorem mem_comap_range_iff {F : OModulePresheaf π} {i : ℕ} (x : LinearMap.ker (F.d K (i + 1))) :
    x ∈ (LinearMap.range (F.d K i)).comap (LinearMap.ker (F.d K (i + 1))).subtype
      ↔ ∃ c, F.d K i c = x.1 := by
  simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range]

theorem d_d_apply (F : OModulePresheaf π) (i : ℕ) (c : F.cochain K i) : F.d K (i + 1) (F.d K i c) = 0 := by
  have h := LinearMap.congr_fun (F.d_comp_d K i) c
  rwa [LinearMap.comp_apply, LinearMap.zero_apply] at h

theorem cochain_ses (i : ℕ) :
    Function.Injective (ιC i) ∧ Function.Surjective (πC i) ∧ LinearMap.range (ιC i) = LinearMap.ker (πC i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f g hfg
    exact funext fun s => S.injective (K.affineInter π s) (congrFun hfg s)
  · intro g
    choose lift hlift using fun s => S.surjective (K.affineInter π s) (g s)
    exact ⟨lift, funext hlift⟩
  · refine le_antisymm ?_ ?_
    · rintro _ ⟨f, rfl⟩
      refine LinearMap.mem_ker.mpr (funext fun s => ?_)
      show S.proj.app (K.affineInter π s) (S.inc.app (K.affineInter π s) (f s)) = 0
      have hzero : S.inc.app (K.affineInter π s) (f s) ∈ LinearMap.ker (S.proj.app (K.affineInter π s)) :=
        (S.exact (K.affineInter π s)) ▸ LinearMap.mem_range_self _ (f s)
      exact hzero
    · intro g hg
      have hgs : ∀ s, g s ∈ LinearMap.range (S.inc.app (K.affineInter π s)) := fun s =>
        (S.exact (K.affineInter π s)).symm ▸ LinearMap.mem_ker.mpr (congrFun (LinearMap.mem_ker.mp hg) s)
      choose lift hlift using hgs
      exact ⟨lift, funext hlift⟩

end AlgebraicGeometry.OModulePresheaf.LES

universe u
open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.OModulePresheaf _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left.AlgebraicGeometry.OModulePresheaf in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.OModulePresheaf _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left.AlgebraicGeometry.OModulePresheaf" in
theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)
    (h₂ : F₂.CechFinite K) (h₃ : F₃.CechFinite K) : F₁.CechFinite K := by
  obtain ⟨δ₀, δ, -, -, h0, hS⟩ := S.exists_connectingHom K
  refine ⟨?_, fun i => ?_⟩
  · haveI : IsNoetherian R (F₂.H0 K) := haveI := h₂.1; isNoetherian_of_isNoetherianRing_of_finite R _
    exact Module.Finite.of_injective (S.inc.kerMap K 0)
      fun x y h => Subtype.ext ((LES.cochain_ses K S 0).1 (congrArg Subtype.val h))
  · rcases i with _ | j
    · haveI := h₃.1; haveI := h₂.2 0
      exact Module.Finite.of_ker_le_range_of_isNoetherianRing δ₀ (S.inc.HSuccMap K 0) h0
    · haveI := h₃.2 j; haveI := h₂.2 (j + 1)
      exact Module.Finite.of_ker_le_range_of_isNoetherianRing (δ j) (S.inc.HSuccMap K (j + 1)) (hS j)
end S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
