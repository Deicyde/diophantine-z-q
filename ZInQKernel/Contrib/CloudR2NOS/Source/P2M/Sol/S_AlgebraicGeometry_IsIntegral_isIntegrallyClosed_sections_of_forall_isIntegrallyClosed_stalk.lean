/-
NOS-CORE PROBE STAGING COPY (lane4, 2026-11-17). NOT an H5 edition:
probe world only; it enters H5 only by the lead binding plus C6 review. No recorded port
SHA exists for this module (lead 2026-11-17T06:06Z). Generated deterministically from the pinned
upstream file by the documented lane4 port transform, as reproduced by the located C5 conformance
pair (Thm/S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_of_iso), numeric options
omitted. SOURCE ONLY, UNCOMPILED. Native HELD.

Vendored, unmodified in substance, from the Fermat's Last Theorem Lean development.

  Source project : https://github.com/anthropics/fermats-last-theorem
  Source revision: 6e837e75355538c7f80bab5b956861e86c4eacc2
  Source file    : P2M/Sol/S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk.lean
  Source sha256  : 66963e705dd1fd57863a92c9c96aebac2788e86b62a82caf721c18224e052f02
  Retrieved      : pinned upstream source revision (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
r2nos_namespace_dual
set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace
r2nos_open_dual "CategoryTheory AlgebraicGeometry TopologicalSpace"

theorem isIntegrallyClosed_of_subsingleton (R : Type u) [CommRing R] [Subsingleton R] : IsIntegrallyClosed R :=
  (isIntegrallyClosed_iff (FractionRing R)).mpr fun {_} _ => ⟨0, Subsingleton.elim _ _⟩

theorem solution {X : Scheme.{u}} [IsIntegral X]
    (h : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) (U : X.Opens) (hU : IsAffineOpen U) :
    IsIntegrallyClosed Γ(X, U) := by
  by_cases hne : Nonempty U
  ·
    haveI := hne
    refine IsIntegrallyClosed.of_localization_maximal fun p _ hp => ?_
    let y : PrimeSpectrum Γ(X, U) := ⟨p, hp.isPrime⟩
    have hy : hU.fromSpec.base y ∈ U := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]
      exact ⟨y, rfl⟩
    obtain ⟨x, hx⟩ : ∃ x : U, hU.primeIdealOf x = y :=
      ⟨⟨hU.fromSpec.base y, hy⟩, hU.fromSpec.injective (by rw [hU.fromSpec_primeIdealOf])⟩
    haveI : IsLocalization.AtPrime (X.presheaf.stalk x.1) p := by
      have := hU.isLocalization_stalk x
      rw [hx] at this
      exact this
    haveI := h x.1
    exact IsIntegrallyClosed.of_equiv
      (IsLocalization.algEquiv p.primeCompl (X.presheaf.stalk x.1) (Localization.AtPrime p)).toRingEquiv
  ·
    have hU0 : U = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hne ⟨⟨z, hz⟩⟩
    subst hU0
    exact isIntegrallyClosed_of_subsingleton _
end S_AlgebraicGeometry_IsIntegral_isIntegrallyClosed_sections_of_forall_isIntegrallyClosed_stalk
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
