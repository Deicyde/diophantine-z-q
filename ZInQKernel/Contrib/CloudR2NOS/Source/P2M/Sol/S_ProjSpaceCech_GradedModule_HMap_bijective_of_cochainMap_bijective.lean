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
  Source file    : P2M/Sol/S_ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective.lean
  Source sha256  : 127ae3c90fcec89d5efd5643e84c0769389135be3a2a812691a2bca5e12c5af0
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 4 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 3 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 multi-command source line(s) split into one command per line (no change of commands).
  * REMOVED source option(s) (default-options rule): `set_option maxHeartbeats 6400000`; `set_option synthInstance.maxHeartbeats 1600000`; `set_option linter.unusedSectionVars false`; `set_option linter.unusedSimpArgs false`; `set_option linter.unusedVariables false`.
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective
r2nos_namespace_dual

set_option autoImplicit false

universe u

noncomputable section

open Finset Function MvPolynomial
r2nos_open_dual "Finset Function MvPolynomial"

namespace ProjSpaceCech
r2nos_namespace_dual
w03_export "ProjSpaceCech" "GradedModule GradedModule.cochain GradedModule.d GradedModule.Hom GradedModule.Hom.cochainMap GradedModule.Hom.cochainMap_comm GradedModule.Hom.cochainMapKer GradedModule.Hom.HMap"
w03_open "ProjSpaceCech"

section HMapBijective

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}

namespace GradedModule
r2nos_namespace_dual
w03_export "ProjSpaceCech.GradedModule" "cochain d Hom Hom.cochainMap Hom.cochainMap_comm Hom.cochainMapKer Hom.HMap mk"
end GradedModule
r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.HMap_bijective_of_cochainMap_bijective' (φ : GradedModule.Hom D₁ D₂)
    (h : ∀ i, Function.Bijective (GradedModule.Hom.cochainMap φ i)) (i : ℕ) :
    Function.Bijective (GradedModule.Hom.HMap φ i) := by
  classical
  have hcomm : ∀ k (x : GradedModule.cochain D₁ k),
      GradedModule.d D₂ k (GradedModule.Hom.cochainMap φ k x)
        = GradedModule.Hom.cochainMap φ (k + 1) (GradedModule.d D₁ k x) := fun k x => by
    rw [← LinearMap.comp_apply, GradedModule.Hom.cochainMap_comm, LinearMap.comp_apply]
  have hker : ∀ k (x : GradedModule.cochain D₁ k),
      GradedModule.Hom.cochainMap φ k x ∈ LinearMap.ker (GradedModule.d D₂ k)
        ↔ x ∈ LinearMap.ker (GradedModule.d D₁ k) := fun k x => by
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hcomm]
    exact ⟨fun hx => (h (k + 1)).1 (by rw [hx, map_zero]), fun hx => by rw [hx, map_zero]⟩
  have hrange : ∀ k (y : GradedModule.cochain D₁ (k + 1)),
      GradedModule.Hom.cochainMap φ (k + 1) y ∈ LinearMap.range (GradedModule.d D₂ k)
        ↔ y ∈ LinearMap.range (GradedModule.d D₁ k) := fun k y => by
    constructor
    · rintro ⟨x', hx'⟩
      obtain ⟨x, rfl⟩ := (h k).2 x'
      exact ⟨x, (h (k + 1)).1 (by rw [← hcomm, hx'])⟩
    · rintro ⟨x, rfl⟩
      exact ⟨GradedModule.Hom.cochainMap φ k x, hcomm k x⟩
  have hkerbij : ∀ k, Function.Bijective (GradedModule.Hom.cochainMapKer φ k) := fun k => by
    constructor
    · intro x y hxy
      exact Subtype.ext ((h k).1 (congrArg Subtype.val hxy))
    · rintro ⟨z, hz⟩
      obtain ⟨x, rfl⟩ := (h k).2 z
      exact ⟨⟨x, (hker k x).mp hz⟩, rfl⟩
  rcases i with _ | j
  · exact hkerbij 0
  · simp only [GradedModule.Hom.HMap]
    constructor
    · refine (injective_iff_map_eq_zero _).mpr fun a ha => ?_
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      have ha' : GradedModule.Hom.cochainMapKer φ (j + 1) x
          ∈ (LinearMap.range (GradedModule.d D₂ j)).comap
              (LinearMap.ker (GradedModule.d D₂ (j + 1))).subtype :=
        (Submodule.Quotient.mk_eq_zero _).mp ha
      rw [Submodule.mem_comap, Submodule.subtype_apply] at ha'
      exact (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr ((hrange j x.1).mp ha'))
    · intro q
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      obtain ⟨x, rfl⟩ := (hkerbij (j + 1)).2 w
      exact ⟨Submodule.Quotient.mk x, rfl⟩

end HMapBijective

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n}
    (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂) (h : ∀ i, Function.Bijective (ProjSpaceCech.GradedModule.Hom.cochainMap φ i)) (i : ℕ) :
    Function.Bijective (ProjSpaceCech.GradedModule.Hom.HMap φ i) :=
  ProjSpaceCech.GradedModule.HMap_bijective_of_cochainMap_bijective' φ h i

end
end S_ProjSpaceCech_GradedModule_HMap_bijective_of_cochainMap_bijective
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
