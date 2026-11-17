/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn (git blob 7128af1e3ae385e0727ff3e252be85930d487157, sha256 605e8b4bab4be94787790ac23b050e0f5a2282fdb38e19846eb663b8092933b6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WindowedSiegelSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ConstantTerm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_FactorizableTestFn
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicBox
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
  AutomorphicForm AutomorphicForm.WindowedSiegel MeasureTheory

theorem AutomorphicForm.norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsFactorizableTestFn K f) (c u : ℝ) (N : ℕ) :
    ∃ C : ℝ, ∀ x ∈ integralWindowedSiegelSet K c u,
      1 ≤ archHeight K (glArch (𝓞 K) K x) →
      ∀ (y : GL (Fin 2) (AdeleRing (𝓞 K) K)),
        ‖(∑' β : K, f (x⁻¹ * unipotentGL2 (algebraMap K (AdeleRing (𝓞 K) K) β) * y))
          - (((adelicAddHaar (𝓞 K) K) (adelicBox K)).toReal : ℂ)⁻¹ *
            ∫ t, f (x⁻¹ * unipotentGL2 t * y) ∂(adelicAddHaar (𝓞 K) K)‖
          ≤ C * (archHeight K (glArch (𝓞 K) K x))⁻¹ ^ N := by
  revert K f hf c u N
  exact @_root_.P2MW.S_AutomorphicForm_norm_tsum_sub_average_le_mul_inv_archHeight_pow_of_isFactorizableTestFn.solution
