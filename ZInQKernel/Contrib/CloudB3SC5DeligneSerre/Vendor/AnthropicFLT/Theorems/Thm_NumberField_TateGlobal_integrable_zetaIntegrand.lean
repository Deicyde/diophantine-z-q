/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_TateGlobal_integrable_zetaIntegrand (git blob fc53ca46d20040ab8494e55116e1c47aebfc540c, sha256 147d0b07aad67c99b5bc949864660cbae7f5532d2a7825e0edadabfd530005e2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_TateGlobal_integrable_zetaIntegrand

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicFourier AutomorphicForm

theorem NumberField.TateGlobal.integrable_zetaIntegrand (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]
    (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure]
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ schwartzBruhat F)
    {χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ} (hχc : Continuous χ) (hχu : IsUnitaryChar (𝓞 F) F χ)
    {s : ℂ} (hs : 1 < s.re) :
    Integrable (fun x : (AdeleRing (𝓞 F) F)ˣ => f x * ((χ x : ℂˣ) : ℂ) * ((ideleNorm F x : ℝ) : ℂ) ^ s) ν := by
  revert F ν f hf χ hχc hχu s hs
  exact @_root_.P2MW.S_NumberField_TateGlobal_integrable_zetaIntegrand.solution
