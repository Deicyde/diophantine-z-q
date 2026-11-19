/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple (git blob a689d2491353cbed56b32a501c3319bd88efa9f4, sha256 d336a48fcc2cea4186727f45d36601daea9fdb61be4027703ed1bd16e95b2f29).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CentreCutSiegelSetAmple
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicLsXi
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ κ : ℝ) (hc : 0 < c) (hd₁ : 0 < d₁)
    (x : AdelicGL2 (𝓞 F) F)
    (hx : ∀ w : InfinitePlace F,
      archComponent F w (glArch (𝓞 F) F x) ∈ rowIsometrySubgroup (w.Completion)) :
    Set.Finite {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      ∃ s ∈ centreCutSiegelSetAmple F c u d₁ d₂ κ,
        globalPoints (𝓞 F) F γ * s ∈ (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ} := by
  revert F c u d₁ d₂ κ hc hd₁ x hx
  exact @_root_.P2MW.S_AutomorphicForm_finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple.solution
