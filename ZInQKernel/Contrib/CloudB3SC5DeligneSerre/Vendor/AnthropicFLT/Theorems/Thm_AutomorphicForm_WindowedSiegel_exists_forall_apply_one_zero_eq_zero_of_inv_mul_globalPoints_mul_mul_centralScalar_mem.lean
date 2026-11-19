/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem (git blob 0b1758f325de30a52d0e11fb775baeb061fc8f0b, sha256 e8867621a64218bc5321927098332d0a1acd172132fd11ce3f397eb569d17734).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WindowedSiegelSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped NumberField

theorem AutomorphicForm.WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem
    (F : Type) [Field F] [NumberField F]
    {C : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)} (hC : IsCompact C) :
    ∃ T₀ : ℝ, ∀ (x y : AutomorphicForm.AdelicGL2 (𝓞 F) F),
      NumberField.AdelicLevel.glFin (𝓞 F) F x ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 F) F →
      NumberField.AdelicLevel.glFin (𝓞 F) F y ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 F) F →
      T₀ < AutomorphicForm.WindowedSiegel.archHeight F (NumberField.AdelicLevel.glArch (𝓞 F) F x) →
      T₀ < AutomorphicForm.WindowedSiegel.archHeight F (NumberField.AdelicLevel.glArch (𝓞 F) F y) →
      ∀ (γ : GL (Fin 2) F) (z : (NumberField.AdeleRing (𝓞 F) F)ˣ),
        x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * y * AutomorphicForm.centralScalar (𝓞 F) F z
            ∈ C →
          (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  revert F C hC
  exact @_root_.P2MW.S_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem.solution
