/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Ihara_amalgamToGamma0Away_surjective (git blob 34e0b5adf93ec9f66ffe4bbbfe146ce5db021b79, sha256 581d85da6febced92b7a0fa25d3c0b3644dc4c13c1e024aa261c700e68162c7c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_Gamma0Away
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_IharaIota
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_IharaAmalgam
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_IharaAmalgamMap
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Ihara_amalgamToGamma0Away_surjective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Ihara.amalgamToGamma0Away_surjective (N q : ℕ) (hNq : Nat.Coprime N q)
    (hq : q.Prime) :
    Function.Surjective (Ihara.amalgamToGamma0Away N q) := by
  revert N q hNq hq
  exact @_root_.P2MW.S_Ihara_amalgamToGamma0Away_surjective.solution
