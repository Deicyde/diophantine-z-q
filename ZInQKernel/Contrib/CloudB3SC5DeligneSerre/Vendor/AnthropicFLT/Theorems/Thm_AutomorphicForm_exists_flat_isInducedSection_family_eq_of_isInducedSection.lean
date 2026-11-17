/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection (git blob 7059835a7ce3df078d9d1fb60f7161687f6807db, sha256 e678276a2dfb6d73f29505df9cbe63958b66f69f813df1a63df918d89ad3a480).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchKFinite
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped NNReal

theorem AutomorphicForm.exists_flat_isInducedSection_family_eq_of_isInducedSection
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (s₀ : ℂ) (φ₀ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ₀ : IsInducedSection (𝓞 F) F (etaFst μ α hα s₀) (etaSnd ν α hα s₀) φ₀)
      (_hφ₀K : IsArchKFinite F φ₀)
      (_hφ₀f : IsKfSmooth F φ₀)
      (_hφ₀c : Continuous φ₀),
    ∃ ψ : ℂ → AdelicGL2 (𝓞 F) F → ℂ,
      ψ s₀ = φ₀
      ∧ (∀ s, IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) (ψ s))
      ∧ (∀ s, IsArchKFinite F (ψ s))
      ∧ (∀ s, IsKfSmooth F (ψ s))
      ∧ Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => ψ p.1 p.2)
      ∧ (∀ g, Differentiable ℂ (fun s => ψ s g))
      ∧ ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          ψ s k = ψ s' k := by
  revert F
  exact @_root_.P2MW.S_AutomorphicForm_exists_flat_isInducedSection_family_eq_of_isInducedSection.solution
