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
  Source file    : P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid.lean
  Source sha256  : 1fb765a49a7a50c384959b4f596e114b6505c790a2ebc24a715ce3a49059e37e
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
  * 4 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
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
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid
r2nos_namespace_dual

set_option autoImplicit false

w03_open "AlgebraicGeometry P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid.AlgebraicGeometry CategoryTheory"

namespace AlgebraicGeometry
r2nos_namespace_dual
w03_export "AlgebraicGeometry" "Surjective Spec Scheme IsSeparated OModulePresheaf.AffSES OModulePresheaf"
namespace OModulePresheaf
r2nos_namespace_dual
w03_export "AlgebraicGeometry.OModulePresheaf" "AffHom AffSES AffHom.cochainMap AffHom.cochainMap_comp_d AffHom.HSuccMap_mk cochain d CechFinite mk d_comp_d"
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

theorem ker_kerMap_le_range (i : ℕ) :
    LinearMap.ker (S.proj.kerMap K i) ≤ LinearMap.range (S.inc.kerMap K i) := by
  intro f hf
  have hf0 : f.1 ∈ LinearMap.range (ιC i) :=
    (cochain_ses K S i).2.2 ▸ LinearMap.mem_ker.mpr (congrArg Subtype.val (LinearMap.mem_ker.mp hf))
  obtain ⟨g, hg⟩ := hf0
  have hgc : g ∈ LinearMap.ker (F₁.d K i) :=
    LinearMap.mem_ker.mpr <| (cochain_ses K S (i + 1)).1 <| by
      rw [← LinearMap.comp_apply, AffHom.cochainMap_comp_d, LinearMap.comp_apply, hg,
        LinearMap.mem_ker.mp f.2, map_zero]
  exact ⟨⟨g, hgc⟩, Subtype.ext hg⟩

theorem ker_HSuccMap_le_range (i : ℕ) :
    LinearMap.ker (S.proj.HSuccMap K i) ≤ LinearMap.range (S.inc.HSuccMap K i) := by
  intro z hz
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hπf : ∃ w, F₃.d K i w = (S.proj.kerMap K (i + 1) f).1 := by
    rw [LinearMap.mem_ker, AffHom.HSuccMap_mk] at hz
    exact (mem_comap_range_iff K _).mp ((Submodule.Quotient.mk_eq_zero _).mp hz)
  obtain ⟨w, hw⟩ := hπf
  obtain ⟨w', hw'⟩ := (cochain_ses K S i).2.1 w
  have hdiff : f.1 - F₂.d K i w' ∈ LinearMap.range (ιC (i + 1)) := by
    rw [(cochain_ses K S (i + 1)).2.2]
    refine LinearMap.mem_ker.mpr ?_
    have hchain := LinearMap.congr_fun (AffHom.cochainMap_comp_d K S.proj i) w'
    simp only [LinearMap.comp_apply] at hchain
    rw [map_sub, hchain, hw', hw]
    exact sub_self _
  obtain ⟨g, hg⟩ := hdiff
  have hgc : g ∈ LinearMap.ker (F₁.d K (i + 1)) :=
    LinearMap.mem_ker.mpr <| (cochain_ses K S (i + 2)).1 <| by
      rw [← LinearMap.comp_apply, AffHom.cochainMap_comp_d, LinearMap.comp_apply, hg,
        map_sub, LinearMap.mem_ker.mp f.2, d_d_apply, sub_zero, map_zero]
  refine ⟨Submodule.Quotient.mk ⟨g, hgc⟩, ?_⟩
  rw [AffHom.HSuccMap_mk]
  refine (Submodule.Quotient.eq _).mpr ((mem_comap_range_iff K _).mpr ⟨-w', ?_⟩)
  show F₂.d K i (-w') = ιC (i + 1) g - f.1
  rw [map_neg, hg]; abel

end AlgebraicGeometry.OModulePresheaf.LES

universe u
open _root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.OModulePresheaf _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid.AlgebraicGeometry.OModulePresheaf in
r2nos_open_dual "_root_.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid.AlgebraicGeometry _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.OModulePresheaf _root_.ZInQ.Contrib.CloudW03NeronSurj.FLT.P2MW.S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid.AlgebraicGeometry.OModulePresheaf" in
theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K : V.OrderedAffineCover)
    (h₁ : F₁.CechFinite K) (h₃ : F₃.CechFinite K) : F₂.CechFinite K :=
  ⟨by haveI := h₁.1; haveI := h₃.1
      exact Module.Finite.of_ker_le_range_of_isNoetherianRing (S.inc.kerMap K 0) (S.proj.kerMap K 0)
        (LES.ker_kerMap_le_range K S 0),
    fun i => by
      haveI := h₁.2 i; haveI := h₃.2 i
      exact Module.Finite.of_ker_le_range_of_isNoetherianRing (S.inc.HSuccMap K i) (S.proj.HSuccMap K i)
        (LES.ker_HSuccMap_le_range K S i)⟩
end S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
