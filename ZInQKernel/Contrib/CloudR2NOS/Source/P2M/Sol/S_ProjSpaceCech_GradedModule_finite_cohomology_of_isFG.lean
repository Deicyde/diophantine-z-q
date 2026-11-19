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
  Source file    : P2M/Sol/S_ProjSpaceCech_GradedModule_finite_cohomology_of_isFG.lean
  Source sha256  : 908faf18acdd51bc3b050dafb1b913198a5e9c992ef800719210966689979542
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
  * 6 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpaceCechTwist
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_finite_H_of_ses
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_ProjSpaceCech_GradedModule_Presentation_ker_isFG
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_ProjSpaceCech_GradedModule_finite_cohomology_pi_FD
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_ProjSpaceCech_GradedModule_finite_cohomology_of_isFG
r2nos_namespace_dual

set_option autoImplicit false

universe u

noncomputable section

open Finset Function MvPolynomial
r2nos_open_dual "Finset Function MvPolynomial"

namespace ProjSpaceCech
r2nos_namespace_dual
w03_export "ProjSpaceCech" "GradedModule GradedModule.H GradedModule.subsingleton_cohomology_of_lt GradedModule.Presentation GradedModule.IsFG GradedModule.Presentation.finite_H_of_ses GradedModule.Presentation.ker_isFG GradedModule.finite_cohomology_pi_FD"
w03_open "ProjSpaceCech"

section Main

variable {R : Type u} [CommRing R] {n : ℕ}

namespace GradedModule
r2nos_namespace_dual
w03_export "ProjSpaceCech.GradedModule" "H subsingleton_cohomology_of_lt Presentation IsFG Presentation.finite_H_of_ses Presentation.ker_isFG finite_cohomology_pi_FD"
end GradedModule
r2nos_open_scoped "ProjSpaceCech.GradedModule" in

theorem GradedModule.finite_cohomology_of_isFG' [IsNoetherianRing R] (D : GradedModule R n)
    (hD : GradedModule.IsFG D) (i : ℕ) :
    Module.Finite R (GradedModule.H D i) := by

  suffices h : ∀ i, ∀ (D' : GradedModule R n), GradedModule.IsFG D' →
      Module.Finite R (GradedModule.H D' i) from h i D hD
  intro i
  induction i using Nat.strong_decreasing_induction with
  | base =>
    refine ⟨n, fun m hm D' _ => ?_⟩
    haveI := GradedModule.subsingleton_cohomology_of_lt D' hm
    infer_instance
  | step i IH =>
    intro D' ⟨σ⟩
    refine GradedModule.Presentation.finite_H_of_ses σ i ?_ ?_
    · exact GradedModule.finite_cohomology_pi_FD R n σ.d₀ i
    · exact IH (i + 1) (Nat.lt_succ_self i) σ.ker (GradedModule.Presentation.ker_isFG σ)

end Main

end ProjSpaceCech

theorem solution {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} (D : ProjSpaceCech.GradedModule R n)
    (hD : ProjSpaceCech.GradedModule.IsFG D) (i : ℕ) : Module.Finite R (ProjSpaceCech.GradedModule.H D i) :=
  ProjSpaceCech.GradedModule.finite_cohomology_of_isFG' D hD i

end
end S_ProjSpaceCech_GradedModule_finite_cohomology_of_isFG
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
