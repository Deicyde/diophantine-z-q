/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral (git blob af6ff6615d7f451ab1a74ad95a6600f81d1e56d3, sha256 cfc1ffc502a8a271cf51cf43366d32c3ca6725b5656c233b9cb582aae2216838).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (g : GL (Fin 2) (v.adicCompletion F))
    (_hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F)
    (_hg' : ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      ∈ v.adicCompletionIntegers F) :
    ∃ (β : GL (Fin 2) (v.adicCompletion F)) (x : v.adicCompletion F),
      (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 ∧
      (∀ i j, (β : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j ∈ v.adicCompletionIntegers F) ∧
      (∀ i j, ((β⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
        ∈ v.adicCompletionIntegers F) ∧
      x ∈ v.adicCompletionIntegers F ∧
      (g = β * gl2Weyl * unipotentGL2 x ∨ g = β * gl2Weyl * unipotentGL2 x * gl2Weyl⁻¹) := by
  revert F v g _hg _hg'
  exact @_root_.P2MW.S_AutomorphicForm_exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral.solution
