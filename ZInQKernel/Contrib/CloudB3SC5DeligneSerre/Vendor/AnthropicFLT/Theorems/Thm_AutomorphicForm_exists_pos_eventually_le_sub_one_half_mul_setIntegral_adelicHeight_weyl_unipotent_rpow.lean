/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow (git blob cf7217d2befe3c52d9af0227458d97a6585519a3, sha256 23092f76e3da714d4f6aa8a26458dd2ae2add6b61143e7e5e2b376aee2d9b57d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHeight
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicHeight IsDedekindDomain
open AutomorphicForm Filter Topology

theorem AutomorphicForm.exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow
    (F : Type) [Field F] [NumberField F]
    (S₁ : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F))
    (hU : ∀ v ∈ S₁, IsOpen (U v) ∧ (U v).Nonempty)
    (U₀ : Set (InfiniteAdeleRing F)) (hU₀ : IsOpen U₀ ∧ U₀.Nonempty) :
    letI := adeleBorel (𝓞 F) F
    ∃ m₀ m₁ : ℝ, 0 < m₀ ∧
      ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ),
        m₀ ≤ (σ - 1 / 2) *
            ∫ x in {x : AdeleRing (𝓞 F) F | x.1 ∈ U₀ ∧ ∀ v ∈ S₁, x.2 v ∈ U v},
              adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ^ (σ + 1 / 2) ∂(adelicAddHaar (𝓞 F) F) ∧
        (σ - 1 / 2) *
            ∫ x, adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ^ (σ + 1 / 2) ∂(adelicAddHaar (𝓞 F) F) ≤ m₁ := by
  revert F S₁ U hU U₀ hU₀
  exact @_root_.P2MW.S_AutomorphicForm_exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow.solution
