/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CohCarrier_heckeT_comm_of_prime (git blob 2474c20bb00895387f868d2f387da9a460270aea, sha256 a6464fd93b6d2bd66b482f1cb143dd19e220ead668d61ca8007e821dfcc19943).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CohCarrier_heckeT_comm_of_prime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem CohCarrier.heckeT_comm_of_prime (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (hℓ : ℓ.Prime) (hcop : Nat.Coprime ℓ ℓ') {V : Type} [AddCommGroup V] (F : H1 M H V) :
    heckeT M H ℓ V (heckeT M H ℓ' V F) = heckeT M H ℓ' V (heckeT M H ℓ V F) := by
  revert M H ℓ ℓ' hℓ hcop V F
  exact @_root_.P2MW.S_CohCarrier_heckeT_comm_of_prime.solution
