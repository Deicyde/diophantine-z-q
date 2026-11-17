/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat (git blob 3ef779cd5738c1e28d85318efd387f4dc621070d, sha256 572f13966b943ff845289984292a0b227b699de1ae6aeacf1982f246c4497900).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SiegelCovering
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat {c u d₁ d₂ : ℝ}
    (hc : c ≤ Real.sqrt 3 / 2) (hu : 1 / 2 ≤ u) (hd₂ : 0 < d₂) (hd : d₁ ≤ d₂) :
    AutomorphicForm.SiegelCovering.CoversModCentre ℚ
      (AutomorphicForm.WindowedSiegel.centreCutSiegelSet ℚ c u d₁ d₂) := by
  revert c u d₁ d₂ hc hu hd₂ hd
  exact @_root_.P2MW.S_AutomorphicForm_SiegelCovering_centreCutSiegelSet_coversModCentre_rat.solution
