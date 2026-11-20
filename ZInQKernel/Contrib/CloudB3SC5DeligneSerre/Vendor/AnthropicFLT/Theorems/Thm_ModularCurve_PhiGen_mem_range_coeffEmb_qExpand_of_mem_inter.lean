/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_PhiGen_mem_range_coeffEmb_qExpand_of_mem_inter (git blob 84c149fbf9b014be9849b88c4f0ca06fc2209318, sha256 fad9137f30349c7b254699b6ca9173d96040f14dd32fafa91abf9b459e24995a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_PhiGen_mem_range_coeffEmb_qExpand_of_mem_inter

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.mem_range_coeffEmb_qExpand_of_mem_inter {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] {f : LaurentSeries K} (h1 : f ∈ Set.range (ModularCurve.qExpand K ℓ)) (h2 : f ∈ Set.range (coeffEmb K)) : ∃ g : LaurentSeries ℚ, f = coeffEmb K (ModularCurve.qExpand ℚ ℓ g) := by
  revert K ℓ hℓ f h1 h2
  exact @_root_.P2MW.S_ModularCurve_PhiGen_mem_range_coeffEmb_qExpand_of_mem_inter.solution
