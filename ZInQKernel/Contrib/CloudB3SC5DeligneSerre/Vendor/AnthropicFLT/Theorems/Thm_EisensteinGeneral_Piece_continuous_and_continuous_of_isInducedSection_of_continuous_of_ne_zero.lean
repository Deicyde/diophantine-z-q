/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinGeneral_Piece_continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero (git blob a55aeb5dee920f8da5116b41b59552b5eff22695, sha256 f021425c397c0b43c2688bc273a4de708b7be7f188e47333842d77d1d6c0a121).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_InducedSection
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_EtaFamily
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinGeneral_Piece_continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField AutomorphicForm

theorem EisensteinGeneral.Piece.continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero
    (F : Type) [Field F]
    [NumberField F] (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
    (hαc : Continuous fun x : (AdeleRing (𝓞 F) F)ˣ => ((α x : ℝˣ) : ℝ))
    (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ) (s₀ : ℂ) (φ₀ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ₀ : IsInducedSection (𝓞 F) F (etaFst μ α hα s₀) (etaSnd ν α hα s₀) φ₀) (hφ₀c : Continuous φ₀)
    (g₀ : AdelicGL2 (𝓞 F) F) (hne : φ₀ g₀ ≠ 0) :
    Continuous μ ∧ Continuous ν := by
  revert F α hα hαc μ ν s₀ φ₀ hφ₀ hφ₀c g₀ hne
  exact @_root_.P2MW.S_EisensteinGeneral_Piece_continuous_and_continuous_of_isInducedSection_of_continuous_of_ne_zero.solution
