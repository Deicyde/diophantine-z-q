/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CohCarrier_exists_gamma0_lift_dvd (git blob ccbdd65460d4b87aef34b4fc53ae91f400063be7, sha256 bf3557dbb45d07760ebb657b18d68700223c7d0b04cf7b6f72454902939e014b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CohCarrier_exists_gamma0_lift_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false
open CongruenceSubgroup
open scoped MatrixGroups

theorem CohCarrier.exists_gamma0_lift_dvd (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (d : (ZMod M)ˣ) :
    ∃ σ : Gamma0 M, gamma0Units M σ = d ∧ ((ℓ * M : ℕ) : ℤ) ∣ ((σ : SL(2, ℤ)) 1 0) := by
  revert M ℓ d
  exact @_root_.P2MW.S_CohCarrier_exists_gamma0_lift_dvd.solution
