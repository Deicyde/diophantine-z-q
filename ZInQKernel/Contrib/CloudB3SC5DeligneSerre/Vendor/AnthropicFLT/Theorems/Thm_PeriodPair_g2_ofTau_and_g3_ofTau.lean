/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PeriodPair_g2_ofTau_and_g3_ofTau (git blob 1e43edcceeef6aa4ee8f0d26d1142abeff595b80, sha256 ca43f65889eceff9f1d4fe9358ed55b70b6869ae308804720660f870110d818a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_PeriodPair_Uniformization
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_PeriodPair_g2_ofTau_and_g3_ofTau

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PeriodPair.g2_ofTau_and_g3_ofTau (τ : UpperHalfPlane) :
    (PeriodPair.ofTau τ).g₂ = 120 * riemannZeta 4 * ModularForm.E₄ τ ∧
      (PeriodPair.ofTau τ).g₃ = 280 * riemannZeta 6 * ModularForm.E₆ τ := by
  revert τ
  exact @_root_.P2MW.S_PeriodPair_g2_ofTau_and_g3_ofTau.solution
