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
  Source file    : Definitions/Def_AlgebraicCurve_FrobeniusEndo.lean
  Source sha256  : 559a6a282e1adf2db1f67ea7356ab0d4ea4e455d2342bd8c4428b3222c46f277
  Retrieved      : pinned read-only clone of the upstream FLT sources (6e837e75), byte-for-byte
  Copyright      : 2026 Anthropic, PBC (see ATTRIBUTION.md of the source for third-party credits)
  Licence        : Apache License, Version 2.0 (see Contrib/CloudW03NeronSurj/LICENSE and NOTICE)

NOTICE OF MODIFICATION (Apache-2.0 §4(b)). This file has been changed from the original
(H5 lane4 port to Lean 4.35.0 / Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679).
Mechanical changes; no statement, hypothesis, definition or proof term was weakened or omitted:
  * 2 `r2nos_namespace_dual` shim line(s) after source `namespace` commands (Mathlib names of the same source namespace stay visible, as in the unprefixed original).
  * 1 import of the lane4 Mathlib-db584 compatibility module `ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal` added (as in every located lane4 port copy).
  * 1 internal `import`(s) retargeted to `ZInQKernel.Contrib.CloudR2NOS.Source.*` / `ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.*` (published W03 duals bound, see ledger) / port utilities.
  * 1 scope(s) the source leaves open at EOF closed explicitly so the port namespace can be closed (no-op in the original).
  * file-level `set_option`s inserted after the port namespace: autoImplicit false; backward.isDefEq.respectTransparency.types false; backward.isDefEq.respectTransparency.instanceSearchTypes false (non-numeric, as in the located C5 conformance copies). NO maxHeartbeats/synthInstance option (numeric options omitted).
  * `import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt` added (port commands) and `open ZInQ.Contrib.CloudW03NeronSurj.FLT` inserted so the source's generalized field notation resolves the isolated declarations exactly as in the unprefixed original.
  * whole file wrapped in `namespace ZInQ.Contrib.CloudW03NeronSurj.FLT … end ZInQ.Contrib.CloudW03NeronSurj.FLT`.
-/

import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib.Algebra.CharP.Reduced
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve
r2nos_namespace_dual

section Package

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (ℓ : ℕ)

structure IsFrobeniusEndo (φ : F →ₐ[K] F) : Prop where

  pow_mem_range : ∀ x : F, ∃ y : F, φ y = x ^ ℓ

  mem_range_pow : ∀ y : F, ∃ x : F, φ y = x ^ ℓ

variable {ℓ : ℕ} {φ : F →ₐ[K] F}

namespace IsFrobeniusEndo
r2nos_namespace_dual

def frobNorm (h : IsFrobeniusEndo ℓ φ) (f : F) : F :=
  (h.pow_mem_range f).choose

theorem map_frobNorm (h : IsFrobeniusEndo ℓ φ) (f : F) : φ (h.frobNorm f) = f ^ ℓ :=
  (h.pow_mem_range f).choose_spec

theorem frobNorm_ne_zero (h : IsFrobeniusEndo ℓ φ) {f : F} (hf : f ≠ 0) :
    h.frobNorm f ≠ 0 := by
  intro h0
  have := h.map_frobNorm f
  rw [h0, map_zero] at this
  exact pow_ne_zero ℓ hf this.symm

theorem isIntegral (h : IsFrobeniusEndo ℓ φ) (hℓ : ℓ ≠ 0) : φ.toRingHom.IsIntegral := by
  intro x
  refine ⟨Polynomial.X ^ ℓ - Polynomial.C (h.frobNorm x), ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C _ hℓ
  · simp [Polynomial.eval₂_sub, h.map_frobNorm x]

end IsFrobeniusEndo

end Package

end AlgebraicCurve
end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
