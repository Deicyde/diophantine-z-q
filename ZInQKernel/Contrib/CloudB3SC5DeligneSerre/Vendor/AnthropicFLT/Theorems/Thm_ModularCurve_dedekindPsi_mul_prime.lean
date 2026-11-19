/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_dedekindPsi_mul_prime (git blob 87e3afe7e9e7086f48c004d11daf8e61697b5e60, sha256 145eaeb63189afda2d10f2b8eb8d0fca6adaefa3c2618d8cd22442aa39baa142).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_dedekindPsi_mul_prime

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open ModularCurve

theorem ModularCurve.dedekindPsi_mul_prime (M ℓ : ℕ) [NeZero M] (hℓ : ℓ.Prime) :
    dedekindPsi (M * ℓ) = (if ℓ ∣ M then ℓ else ℓ + 1) * dedekindPsi M := by
  revert M ℓ hℓ
  exact @_root_.P2MW.S_ModularCurve_dedekindPsi_mul_prime.solution
