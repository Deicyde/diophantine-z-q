/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_TateCurve_symAddHyps_unconditional (git blob 4748715d01284a0ee2aef39e7f0d3a32286036bb, sha256 a559cc846dcf1f143ca267afde1e7cfe581fd6ffc36f9435fa6f8f8a90eb1d08).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_TateCurve_XMultSeparation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_symAdd_sum_allParams_unconditional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_TateCurve_diffHyp_unconditional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_TateCurve_symAddHyps_unconditional

open TateCurve
open scoped NNReal

theorem solution {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    [CharZero K] [DecidableEq K] [IsAlgClosed K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) :
    SymAddHyps q := by
  have hqR : ‖q‖ < 1 := by exact_mod_cast hq
  exact symAddHyps_of_sum_diff_of_isAlgClosed hq0 hq
    (symAdd_sum_allParams_unconditional hq0 hqR)
    (diffHyp_unconditional hq0 hqR)
