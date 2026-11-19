/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_exists_continuousOn_exp_eq_rayClassLSeries (git blob c140571af36bff9ad98f7c5c83072c2384469290, sha256 fd0fd915e8695c3a0cc22e4b770a7772594400fea066cf3c8959aa6f5234fd0c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_CompletedRayL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_RayCharacterData
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField IsDedekindDomain Deep.NTSupply
open scoped nonZeroDivisors

theorem NumberField.exists_continuousOn_exp_eq_rayClassLSeries
    (K : Type) [Field K] [NumberField K] (𝔣 : Ideal (𝓞 K)) (h𝔣 : 𝔣 ≠ ⊥)
    (χ : NarrowRayClassGroup K 𝔣 →* ℂ) :
    ∃ Λ : ℝ → ℂ, ContinuousOn Λ (Set.Ioi 1) ∧
      (∀ s : ℝ, 1 < s → Complex.exp (Λ s) = M4aTorus.rayClassLSeries K 𝔣 χ s) ∧
      (∀ s : ℝ, 1 < s → Summable fun v : HeightOneSpectrum (𝓞 K) =>
          M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
            (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))) ∧
      ∃ C : ℝ, ∀ s : ℝ, 1 < s →
        ‖Λ s - ∑' v : HeightOneSpectrum (𝓞 K),
            M4aP2.chiIdeal K 𝔣 χ (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K) *
              (Ideal.absNorm v.asIdeal : ℂ) ^ (-(s : ℂ))‖ ≤ C := by
  revert K 𝔣 h𝔣 χ
  exact @_root_.P2MW.S_NumberField_exists_continuousOn_exp_eq_rayClassLSeries.solution
