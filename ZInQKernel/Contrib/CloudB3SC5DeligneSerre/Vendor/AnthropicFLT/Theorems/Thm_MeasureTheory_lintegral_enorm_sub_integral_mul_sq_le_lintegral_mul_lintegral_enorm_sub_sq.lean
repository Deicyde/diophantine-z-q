/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MeasureTheory_lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq (git blob c2787a62592ce74ece10547ecee1d08d429fd1a8, sha256 94518ef1091cd8546cd408d51dc8816477c0df4fc160ee21fe5c0420afea6092).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_MeasureTheory_lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal

theorem MeasureTheory.lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq
    {X A : Type*} [MeasurableSpace X] [MeasurableSpace A] (ν : Measure X) (ρ : Measure A) [SFinite ν] [SFinite ρ]
    (p : A → ℝ) (hp : Measurable p) (hp0 : ∀ a, 0 ≤ p a) (hp1 : ∫ a, p a ∂ρ = 1)
    (u : X → ℂ) (hu : Measurable u) (U : X → A → ℂ) (hU : Measurable (Function.uncurry U))
    (hint : ∀ x, Integrable (fun a => U x a * (p a : ℂ)) ρ) :
    ∫⁻ x, ‖u x - ∫ a, U x a * (p a : ℂ) ∂ρ‖ₑ ^ 2 ∂ν
      ≤ ∫⁻ a, ENNReal.ofReal (p a) * ∫⁻ x, ‖u x - U x a‖ₑ ^ 2 ∂ν ∂ρ := by
  revert X A ν ρ p hp hp0 hp1 u hu U hU hint
  exact @_root_.P2MW.S_MeasureTheory_lintegral_enorm_sub_integral_mul_sq_le_lintegral_mul_lintegral_enorm_sub_sq.solution
