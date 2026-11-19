/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet (git blob b599fda042a47133002983f50d894e088ea375d1, sha256 ae24b51c0551e41864d19da20f75479cc83dbd4984b4e521aa681d8f20ce5a7c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CentreCutSiegelSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHeight
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicHeight
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (hc : 0 < c) (t : AdelicGL2 (𝓞 F) F)
    (σ : ℝ) (hσ : 1 / 2 < σ) :
    letI := adeleBorel (𝓞 F) F
    ∃ C : ℝ, ∀ s ∈ centreCutSiegelSet F c u d₁ d₂,
      Summable (fun ξ : F => adelicHeight F (adelicWeyl (𝓞 F) F
          * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (s * t)) ^ (σ + 1 / 2)) ∧
      adelicHeight F (s * t) ^ (σ + 1 / 2)
          + ∑' ξ : F, adelicHeight F (adelicWeyl (𝓞 F) F
              * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * (s * t)) ^ (σ + 1 / 2)
        ≤ C * archHeight F (glArch (𝓞 F) F s) ^ (σ + 1 / 2) := by
  revert F c u d₁ d₂ hc t σ hσ
  exact @_root_.P2MW.S_AutomorphicForm_exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet.solution
