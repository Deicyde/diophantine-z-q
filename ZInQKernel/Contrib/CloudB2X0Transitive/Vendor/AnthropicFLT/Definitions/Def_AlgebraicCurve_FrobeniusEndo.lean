/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Definitions.Def_AlgebraicCurve_FrobeniusEndo
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib.Algebra.CharP.Reduced

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section Package

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (ℓ : ℕ)

structure IsFrobeniusEndo (φ : F →ₐ[K] F) : Prop where

  pow_mem_range : ∀ x : F, ∃ y : F, φ y = x ^ ℓ

  mem_range_pow : ∀ y : F, ∃ x : F, φ y = x ^ ℓ

variable {ℓ : ℕ} {φ : F →ₐ[K] F}

namespace IsFrobeniusEndo

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
