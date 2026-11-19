/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test (git blob a15f3c52c74e5a7968f3eafaa69f26048961d1c8, sha256 5404bf91344aebf49164caae0d33ffc21fc9de443f7ec87ca3333fc817f69365).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FrobeniusDensity_PrimeSums
import Mathlib.NumberTheory.NumberField.DedekindZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField
theorem FrobeniusDensity.tendsto_sub_one_mul_idealSum_test
    (K : Type*) [Field K] [NumberField K] :
    Filter.Tendsto (fun s : ℝ => (s - 1) * (FrobeniusDensity.idealSum K s).toReal)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (dedekindZeta_residue K)) := by
  revert K
  exact @_root_.P2MW.S_FrobeniusDensity_tendsto_sub_one_mul_idealSum_test.solution
