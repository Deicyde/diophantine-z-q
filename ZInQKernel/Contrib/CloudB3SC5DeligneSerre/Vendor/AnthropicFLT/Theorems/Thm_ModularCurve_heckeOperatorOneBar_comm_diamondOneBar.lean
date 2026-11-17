/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_heckeOperatorOneBar_comm_diamondOneBar (git blob 59fa57e2bd5f07ac3a2673e559e26d9a4d6a3f95, sha256 fa178b74352c3bdd8636f4f83ad3010c2340fe93359ca1b54115164990a6f35d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_heckeOperatorOneBar_comm_diamondOneBar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.heckeOperatorOneBar_comm_diamondOneBar (M : ℕ) [NeZero M] (ℓ : Nat.Primes)
    (d : ℕ) :
    ModularCurve.heckeOperatorOneBar M ℓ * ModularCurve.diamondOneBar M d =
      ModularCurve.diamondOneBar M d * ModularCurve.heckeOperatorOneBar M ℓ := by
  revert M ℓ d
  exact @_root_.P2MW.S_ModularCurve_heckeOperatorOneBar_comm_diamondOneBar.solution
