/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CohCarrier_heckeT_diamondRaw_comm (git blob bbe36e59bcf854bbbcca65e98b77fb144ed5bd2d, sha256 0b4ee79485d9811f66b8c6d63358556374900db6dfdaf4aedb6f3f975bf4fadc).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CohCarrier_heckeT_diamondRaw_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem CohCarrier.heckeT_diamondRaw_comm (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (σ : CongruenceSubgroup.Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0)
    {V : Type} [AddCommGroup V] (F : H1 M H V) :
    heckeT M H ℓ V (diamondRaw M H V σ F) = diamondRaw M H V σ (heckeT M H ℓ V F) := by
  revert M H ℓ σ hσ V F
  exact @_root_.P2MW.S_CohCarrier_heckeT_diamondRaw_comm.solution
