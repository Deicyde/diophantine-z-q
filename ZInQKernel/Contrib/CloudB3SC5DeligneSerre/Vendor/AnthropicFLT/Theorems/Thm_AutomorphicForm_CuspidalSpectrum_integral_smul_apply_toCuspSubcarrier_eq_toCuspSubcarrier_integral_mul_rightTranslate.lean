/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate (git blob 9b0f896f994843c4d760ae4fc6889603bcb231f2, sha256 f026f5ef56b79ebacafd4411bcffb0407c93b76c232cd3f7260e28eb6275c946).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalSpectrumSubrep
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

theorem AutomorphicForm.CuspidalSpectrum.integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate
    (F : Type) [Field F] [NumberField F] {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)}
    (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀) (σ : ℝ)
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)] [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) [IsFiniteMeasure μ]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (π : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → (↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)))
    (hπ : ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), IsCuspLift F hΦ₀ σ ξ (rightTranslate F (adelicArchGLIncl F (ι κ))) (π κ))
    (hπc : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), Continuous fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => π κ v)
    (c : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ) (hc : Continuous c)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ) :
    ∃ h : (fun x => ∫ κ, c κ * φ (x * adelicArchGLIncl F (ι κ)) ∂μ) ∈ cuspMemberSubmodule F Φ₀ ξ,
      ∫ κ, c κ • π κ (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩) ∂μ =
        toCuspSubcarrier F hΦ₀ σ ξ ⟨fun x => ∫ κ, c κ * φ (x * adelicArchGLIncl F (ι κ)) ∂μ, h⟩ := by
  revert F α β Φ₀ hΦ₀ σ ξ μ ι hι π hπ hπc c hc φ hφ
  exact @_root_.P2MW.S_AutomorphicForm_CuspidalSpectrum_integral_smul_apply_toCuspSubcarrier_eq_toCuspSubcarrier_integral_mul_rightTranslate.solution
