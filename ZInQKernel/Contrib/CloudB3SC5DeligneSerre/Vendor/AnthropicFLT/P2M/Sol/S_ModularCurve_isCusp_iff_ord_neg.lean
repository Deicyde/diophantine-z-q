/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_isCusp_iff_ord_neg (git blob da1ae8e3bdbb98e38eb3265f52f5655bc0e24e21, sha256 4f55978b0c020e651cb5df6c1ebf4ed5e4cfd78e074fec1d612769ac52d8f9f8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QAdicPlace
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_mem_iff_ord_nonneg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_isCusp_iff_ord_neg

open ModularCurve AlgebraicCurve

theorem solution {K : Type*} {E : Type*} [Field K] [Field E] [Algebra K E] (j : E) (v : Place K E) : IsCusp j v ↔ v.ord j < 0 := by
  rcases eq_or_ne j 0 with rfl | hj
  · rw [isCusp_iff, Place.ord_zero]
    exact ⟨fun h => (h (zero_mem _)).elim, fun h => (lt_irrefl _ h).elim⟩
  · rw [isCusp_iff, v.mem_iff_ord_nonneg hj, not_le]
