/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_transcendental_jqN (git blob e2a26952f0837dd588bf41f59cfc1fbc6150a0d7, sha256 93bd4f975413711083b066d0bb7037debfb222b8241341950ada5a4a485f8a5c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_aeval_jq_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_transcendental_jqN

open ModularCurve IntermediateField

noncomputable section

theorem solution (N : ℕ) [NeZero N] : Transcendental ℚ (jqN N) :=by
  refine transcendental_iff.mpr fun p hp => ?_
  refine ModularCurve.aeval_jq_eq_zero (p := p) (qExpand_injective N ?_)
  rw [map_zero]
  calc qExpand ℚ N (Polynomial.aeval jq p)
      = qExpandₐ N (Polynomial.aeval jq p) := rfl
    _ = Polynomial.aeval (qExpandₐ N jq) p := (Polynomial.aeval_algHom_apply _ _ _).symm
    _ = Polynomial.aeval (jqN N) p := rfl
    _ = 0 := hp

end
