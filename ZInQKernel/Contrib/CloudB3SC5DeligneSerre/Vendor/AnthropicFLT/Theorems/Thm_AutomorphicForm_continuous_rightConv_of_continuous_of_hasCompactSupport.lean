/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport (git blob 9afe3ec0a9772fa50f1ad497d4b0143f435199b1, sha256 2872db35124076705713349aa4ce2b74aa10aae243a14140f868b7a4dc867502).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RightConvolution
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

theorem AutomorphicForm.continuous_rightConv_of_continuous_of_hasCompactSupport
    (F : Type) [Field F] [NumberField F]
    (φ : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hφ : Continuous φ)
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Continuous (AutomorphicForm.rightConv F φ g) := by
  revert F φ hφ g hg hgc
  exact @_root_.P2MW.S_AutomorphicForm_continuous_rightConv_of_continuous_of_hasCompactSupport.solution
