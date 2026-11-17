/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_toricPoint_snd_coeff_of_not_dvd (git blob 38e7d615593022e5377a81d63922bc809e088f52, sha256 7b9793093a72192fcd3c6cd278c0d6fd6110415c510a77ad53825235135403aa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_toricPoint_snd_coeff_of_not_dvd

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve
theorem ModularCurve.toricPoint_snd_coeff_of_not_dvd (K : Type*) [Field K] (p : ℕ) (c : K) {m : ℕ} (hpm : ¬ p ∣ m) : (toricPoint K p c).2.coeff (m : ℤ) = 0 := by
  revert K p c m hpm
  exact @_root_.P2MW.S_ModularCurve_toricPoint_snd_coeff_of_not_dvd.solution
