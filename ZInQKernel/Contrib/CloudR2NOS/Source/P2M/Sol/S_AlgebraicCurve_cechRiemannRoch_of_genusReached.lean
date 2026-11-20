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
  Source file    : P2M/Sol/S_AlgebraicCurve_cechRiemannRoch_of_genusReached.lean
  Source sha256  : dd458800da628b8173adaaea51c32e3fc968b89f5d57a86014f7993b12a237bd
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 1 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 `r2nos_open_dual`/`r2nos_open_scoped_dual` shim line(s) after source `open` commands (completes each opened namespace by its other half where the port splits one source root namespace between Mathlib root and the prefix).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 13 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 2 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_TwoChartCech
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_finite_H1_of_genusReached
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicCurve_cechH1ToH1_bijective
import ZInQKernel.Contrib.CloudW03NeronSurj.PortUtil
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace P2MW.S_AlgebraicCurve_cechRiemannRoch_of_genusReached
r2nos_namespace_dual

set_option autoImplicit false

open AlgebraicCurve in
r2nos_open_dual "AlgebraicCurve" in
theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) :
    FiniteDimensional K ↥(cechH0 S₀ S₁ D) ∧ Module.Finite K (cechH1 S₀ S₁ D) ∧
      Module.finrank K ↥(cechH0 S₀ S₁ D) = ell D ∧
      Module.finrank K (cechH1 S₀ S₁ D) = indexOfSpecialty D ∧
      (Module.finrank K ↥(cechH0 S₀ S₁ D) : ℤ) - Module.finrank K (cechH1 S₀ S₁ D)
        = Divisor.degree D + 1 - γ ∧
      (D₀ ≤ D → Subsingleton (cechH1 S₀ S₁ D)) := by
  obtain ⟨v₀, hv₀⟩ := h₀
  haveI : Nonempty (Place K F) := ⟨v₀⟩
  haveI : FiniteDimensional K ↥(LSpace D) := finiteDimensional_lSpace (K := K) (F := F) D
  haveI : Module.Finite K (H1 D) := finite_H1_of_genusReached h D
  let e0 := cechH0Equiv hcover D
  let e1 : cechH1 S₀ S₁ D ≃ₗ[K] H1 D :=
    LinearEquiv.ofBijective (cechH1ToH1 hcover D) (cechH1ToH1_bijective h hcover ⟨v₀, hv₀⟩ h₁ D)
  haveI : Module.Finite K (cechH1 S₀ S₁ D) := Module.Finite.equiv e1.symm
  have h0 : Module.finrank K ↥(cechH0 S₀ S₁ D) = ell D := e0.finrank_eq
  have h1 : Module.finrank K (cechH1 S₀ S₁ D) = indexOfSpecialty D := by
    rw [e1.finrank_eq, indexOfSpecialty_eq_finrank_H1]
  obtain ⟨-, hidx⟩ := indexOfSpecialty_eq_of_genusReached h D
  refine ⟨LinearEquiv.finiteDimensional e0.symm, inferInstance, h0, h1, ?_, fun hD => ?_⟩
  · rw [h0, h1]; omega
  · have hreach := h.eq_of_ge hD
    have hi0 : Module.finrank K (cechH1 S₀ S₁ D) = 0 := by
      have : (indexOfSpecialty D : ℤ) = 0 := by rw [hidx]; omega
      rw [h1]; exact_mod_cast this
    exact Module.finrank_zero_iff.mp hi0
end S_AlgebraicCurve_cechRiemannRoch_of_genusReached
end P2MW

end ZInQ.Contrib.CloudW03NeronSurj.FLT
