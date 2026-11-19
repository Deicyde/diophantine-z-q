/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CohCarrier_diamondRaw_comm (git blob 80388457327013e3d5b6f288a2fc948dba37f23f, sha256 10eb7688095069498f996219c8f491ab2c29f3c8f1e21b361b9044ca0f3e7ec1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CohCarrier_diamondRaw_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem CohCarrier.diamondRaw_comm (M : ℕ) (H : Subgroup (ZMod M)ˣ) (σ σ' : CongruenceSubgroup.Gamma0 M)
    {V : Type} [AddCommGroup V] (F : H1 M H V) :
    diamondRaw M H V σ (diamondRaw M H V σ' F) = diamondRaw M H V σ' (diamondRaw M H V σ F) := by
  revert M H σ σ' V F
  exact @_root_.P2MW.S_CohCarrier_diamondRaw_comm.solution
