/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalConstituent_forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists (git blob 039b2d89e482c811e34b5c3b32d5d3c195acc718, sha256 2ea8445c9cdb88f578bedd3818dadcba65971a15a00617b838a09668d6c06f32).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalConstituent_forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField AutomorphicForm IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F pins ξ V)
    (w : InfinitePlace F) (hw : w.IsReal)
    (x₀ : AdelicGL2 (𝓞 F) F → ℂ) (hx₀ : x₀ ∈ V) (hne : x₀ ≠ 0)
    (hinv : ∀ (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ), Matrix.GeneralLinearGroup.det h = 1 →
      x₀ (g * archRealGLAt hw h) = x₀ g)
    (x : AdelicGL2 (𝓞 F) F → ℂ) (hx : x ∈ V)
    (g : AdelicGL2 (𝓞 F) F) (h : GL (Fin 2) ℝ) (hh : Matrix.GeneralLinearGroup.det h = 1) :
    x (g * archRealGLAt hw h) = x g := by
  revert F pins ξ V hV w hw x₀ hx₀ hne hinv x hx g h hh
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalConstituent_forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists.solution
