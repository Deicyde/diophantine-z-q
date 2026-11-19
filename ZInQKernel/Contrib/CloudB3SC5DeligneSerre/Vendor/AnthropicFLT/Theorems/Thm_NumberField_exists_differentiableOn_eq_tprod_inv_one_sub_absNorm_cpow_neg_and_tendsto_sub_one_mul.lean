/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul (git blob 5f52b459faa731c5a8870e76b2030cc3fb94cf53, sha256 b8569a1c1dd355faa8253de8a95f3496872dbeed3c817e274085c63ad36395a9).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open IsDedekindDomain NumberField Filter Topology

theorem NumberField.exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul (K : Type) [Field K] [NumberField K]
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L ({s : ℂ | 1 / 2 < s.re} \ {1}) ∧
      (∀ s : ℂ, 1 < s.re →
        L s = ∏' v : {v : HeightOneSpectrum (𝓞 K) // v ∉ T},
          (1 - ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))⁻¹) ∧
      ∃ κ : ℂ, κ ≠ 0 ∧ Tendsto (fun s : ℂ => (s - 1) * L s) (𝓝[≠] 1) (𝓝 κ) := by
  revert K T
  exact @_root_.P2MW.S_NumberField_exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul.solution
