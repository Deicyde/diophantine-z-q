/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_heckeOperatorOneBar_comm (git blob a7c3df29f83a15429be088980a38a0acf28f3acb, sha256 f591bece49a3441f5d90a7a34932ec7ff3acde0b0285aaadb0fb570bb8d40461).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_heckeOperatorOneBar_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.heckeOperatorOneBar_comm (M : ℕ) [NeZero M] (ℓ ℓ' : Nat.Primes) :
    ModularCurve.heckeOperatorOneBar M ℓ * ModularCurve.heckeOperatorOneBar M ℓ' =
      ModularCurve.heckeOperatorOneBar M ℓ' * ModularCurve.heckeOperatorOneBar M ℓ := by
  revert M ℓ ℓ'
  exact @_root_.P2MW.S_ModularCurve_heckeOperatorOneBar_comm.solution
