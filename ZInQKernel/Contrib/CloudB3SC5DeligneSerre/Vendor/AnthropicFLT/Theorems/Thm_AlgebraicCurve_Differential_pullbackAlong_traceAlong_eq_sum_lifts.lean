/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_sum_lifts (git blob b548e75027225ab2137c1f95461c3f5aadb74ad3, sha256 07d6f82aba6460c4abac2aa2515f8f402d3268deaf6925aafd1f5e240c4e5936).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DifferentialPushPull
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_sum_lifts

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.Differential.pullbackAlong_traceAlong_eq_sum_lifts
    (K F F' E : Type*) [Field K] [Field F] [Field F'] [Field E]
    [Algebra K F] [Algebra K F'] [Algebra K E] [IsAlgClosed E]
    (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (e : F →ₐ[K] E) (S : Finset (F' →ₐ[K] E)) (hS : ∀ σ : F' →ₐ[K] E, σ ∈ S ↔ σ.comp φ = e)
    (ω' : Ω[F'⁄K]) :
    Differential.pullbackAlong e (Differential.traceAlong φ ω') =
      ∑ σ ∈ S, Differential.pullbackAlong σ ω' := by
  revert K F F' E φ hfin hsep e S hS ω'
  exact @_root_.P2MW.S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_sum_lifts.solution
