/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_toricPoint_snd_coeff_zero (git blob ffbae7eeee1b8a24e3efe7766166e95d82dfa447, sha256 9ab912f4bd0b94e748e9bff6cef9a96715c6ed49693a86bbd4b95dc860792cbd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_toricPoint_snd_coeff_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.toricPoint_snd_coeff_zero (K : Type*) [Field K] (p : ℕ) (c : K) : (toricPoint K p c).2.coeff 0 = c ^ 2 / (1 - c) ^ 3 := by
  revert K p c
  exact @_root_.P2MW.S_ModularCurve_toricPoint_snd_coeff_zero.solution
