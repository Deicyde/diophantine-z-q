/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_PhiGen_mem_range_coeffEmb_of_forall_coeffMap_eq (git blob c8c5d483d39176c65825161704b968d2c8de1d4e, sha256 ace394dbad9efe601d399da00c8ecdaf73269a9b4c79742cab12ad59db835a57).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_PhiGen_mem_range_coeffEmb_of_forall_coeffMap_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve ModularCurve.PhiGen
theorem ModularCurve.PhiGen.mem_range_coeffEmb_of_forall_coeffMap_eq {K : Type*} [Field K] [Algebra ℚ K] (hfix : ∀ c : K, (∀ σ : K ≃ₐ[ℚ] K, σ c = c) → ∃ r : ℚ, algebraMap ℚ K r = c) {f : LaurentSeries K} (hf : ∀ σ : K ≃ₐ[ℚ] K, coeffMap (σ : K →+* K) f = f) : f ∈ Set.range (coeffEmb K) := by
  revert K hfix f hf
  exact @_root_.P2MW.S_ModularCurve_PhiGen_mem_range_coeffEmb_of_forall_coeffMap_eq.solution
