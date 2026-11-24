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
  Source file    : P2M/Sol/S_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections.lean
  Source sha256  : c3faa457a3c79d272f8cbd11ee6fa92e24fab9b3825572852fea4c27ee65f1d9
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 3 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
r2nos_namespace_dual

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
r2nos_open_dual "CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace"

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsIntegral X] [IsIntegral Y]
    (hY : ∀ V : Y.Opens, IsAffineOpen V → IsIntegrallyClosed Γ(Y, V))
    (U : X.Opens) (hU : IsAffineOpen U) : IsIntegrallyClosed Γ(X, U) := by
  refine AlgebraicGeometry.IsIntegral.isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
    (X := X) (fun x => ?_) U hU

  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  replace hV : IsAffineOpen (V : Y.Opens) := hV

  haveI : IsAffine (V : Scheme.{u}) := hV
  have hne : Nonempty (V : Scheme.{u}) := ⟨⟨f.base x, hxV⟩⟩
  haveI : IsIntegral (V : Scheme.{u}) := isIntegral_of_isOpenImmersion (Scheme.Opens.ι V)
  haveI : IsDomain Γ((V : Scheme.{u}), ⊤) := inferInstance
  haveI : IsIntegrallyClosed Γ((V : Scheme.{u}), ⊤) := by
    haveI : IsIntegrallyClosed Γ(Y, V) := hY V hV
    exact IsIntegrallyClosed.of_equiv (Scheme.Opens.topIso V).commRingCatIsoToRingEquiv.symm

  haveI : Smooth (f ∣_ V) := inferInstance
  have hx' : x ∈ f ⁻¹ᵁ V := hxV
  have h2 := (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk (f ∣_ V) ⟨x, hx'⟩).2
  have e2 : ((f ⁻¹ᵁ V : X.Opens) : Scheme.{u}).presheaf.stalk ⟨x, hx'⟩ ≅ X.presheaf.stalk x :=
    (f ⁻¹ᵁ V).stalkIso ⟨x, hx'⟩
  haveI := h2
  exact IsIntegrallyClosed.of_equiv e2.commRingCatIsoToRingEquiv

#print axioms solution
end S_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
