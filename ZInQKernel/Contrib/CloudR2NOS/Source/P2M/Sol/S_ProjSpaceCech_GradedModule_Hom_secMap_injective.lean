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
  Source file    : P2M/Sol/S_ProjSpaceCech_GradedModule_Hom_secMap_injective.lean
  Source sha256  : 6f7d7f57e09e77053892783a93445a10af38096a277a704b5a0931343aa55751
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 6 `p2m_*` command/tactic occurrence(s) renamed to the H76 `w03_*` / lane4 `r2nos_*` port commands.
  * 4 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
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

namespace P2MW.S_ProjSpaceCech_GradedModule_Hom_secMap_injective
r2nos_namespace_dual

set_option autoImplicit false

universe u

noncomputable section

open Finset Function MvPolynomial
r2nos_open_dual "Finset Function MvPolynomial"

namespace ProjSpaceCech
r2nos_namespace_dual
w03_export "ProjSpaceCech" "GradedModule GradedModule.Frac GradedModule.sec GradedModule.sec.mk GradedModule.sec_mk_eq GradedModule.Hom GradedModule.Hom.map_monMul GradedModule.Hom.secMap"
w03_open "ProjSpaceCech"

section SecMapInj

variable {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : GradedModule R n}

namespace GradedModule
r2nos_namespace_dual
w03_export "ProjSpaceCech.GradedModule" "Frac sec sec.mk sec_mk_eq Hom Hom.map_monMul Hom.secMap mk"
namespace Hom
r2nos_namespace_dual
w03_export "ProjSpaceCech.GradedModule.Hom" "map_monMul secMap mem_grade mk toLinearMap"
end GradedModule.Hom
r2nos_open_scoped "ProjSpaceCech.GradedModule ProjSpaceCech.GradedModule.Hom" in
theorem GradedModule.Hom.secMap_mk (φ : GradedModule.Hom D₁ D₂) (I : Finset (Fin (n + 1)))
    (x : GradedModule.Frac D₁ I) :
    GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I x)
      = GradedModule.sec.mk D₂ I ⟨x.denExp, x.hden, φ.toLinearMap x.num, φ.mem_grade _ _ x.hnum⟩ := rfl

r2nos_open_scoped "ProjSpaceCech.GradedModule ProjSpaceCech.GradedModule.Hom" in

theorem GradedModule.Hom.secMap_injective' (φ : GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap) (I : Finset (Fin (n + 1))) :
    Function.Injective (GradedModule.Hom.secMap φ I) := by
  intro p q h
  obtain ⟨x, rfl⟩ := Quotient.exists_rep p
  obtain ⟨y, rfl⟩ := Quotient.exists_rep q
  change GradedModule.sec.mk D₁ I x = GradedModule.sec.mk D₁ I y
  change GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I x)
    = GradedModule.Hom.secMap φ I (GradedModule.sec.mk D₁ I y) at h
  rw [GradedModule.Hom.secMap_mk, GradedModule.Hom.secMap_mk, GradedModule.sec_mk_eq] at h
  obtain ⟨c, hc, heq⟩ := h
  refine (GradedModule.sec_mk_eq D₁ I).mpr ⟨c, hc, hinj ?_⟩
  rw [GradedModule.Hom.map_monMul, GradedModule.Hom.map_monMul]
  exact heq

end SecMapInj

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] {n : ℕ} {D₁ D₂ : ProjSpaceCech.GradedModule R n} (φ : ProjSpaceCech.GradedModule.Hom D₁ D₂)
    (hinj : Function.Injective φ.toLinearMap) (I : Finset (Fin (n + 1))) :
    Function.Injective (ProjSpaceCech.GradedModule.Hom.secMap φ I) :=
  ProjSpaceCech.GradedModule.Hom.secMap_injective' φ hinj I

end
end S_ProjSpaceCech_GradedModule_Hom_secMap_injective
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
