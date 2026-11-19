/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one (git blob 6e1732c30b72655c2a46dfa85c272f5188732e29, sha256 b4ffbdfb2c31fc3f4853990e6456bbdf35828a874ff429a4f645933419c5fade).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem NumberField.multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one
    (M : Type) [Field M] [NumberField M] (S : Finset (HeightOneSpectrum (𝓞 M)))
    (z : {v : HeightOneSpectrum (𝓞 M) // v ∉ S} → ℂ) (hz : ∀ v, ‖z v‖ ≤ 1) :
    (∀ s : ℂ, 1 < s.re →
        Multipliable (fun v : {v : HeightOneSpectrum (𝓞 M) // v ∉ S} =>
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)) ∧
      DifferentiableOn ℂ
        (fun s : ℂ => ∏' v : {v : HeightOneSpectrum (𝓞 M) // v ∉ S},
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹)
        {s : ℂ | 1 < s.re} ∧
      ∀ s : ℂ, 1 < s.re →
        (∏' v : {v : HeightOneSpectrum (𝓞 M) // v ∉ S},
          (1 - z v * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) ≠ 0 := by
  revert M S z hz
  exact @_root_.P2MW.S_NumberField_multipliable_differentiableOn_tprod_ne_zero_eulerProduct_of_norm_le_one.solution
