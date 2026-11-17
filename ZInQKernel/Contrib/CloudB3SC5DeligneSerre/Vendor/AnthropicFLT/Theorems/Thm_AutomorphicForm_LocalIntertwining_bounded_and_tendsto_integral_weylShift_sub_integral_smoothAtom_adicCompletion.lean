/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion (git blob c87123178f377221468a242d6e4458c7e4d58246, sha256 59d020e375e0e2c02e05cb8864381af82686110fefd90c52a0c479bb9a7094ba).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicHaar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open scoped NNReal

theorem AutomorphicForm.LocalIntertwining.bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]
    (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure]
    (m : ℕ) (_hm : 1 ≤ m)
    (A B : v.adicCompletion F → ℂ)
    (_hA : ∀ x ∈ v.adicCompletionIntegers F, ∀ y ∈ v.adicCompletionIntegers F,
      Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → A y = A x)
    (_hB : ∀ x y : v.adicCompletion F, Valued.v (y - x) ≤ Multiplicative.ofAdd (-(m : ℤ)) → B y = B x) :
    let a : ℝ → v.adicCompletion F → ℂ := fun σ x =>
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)).indicator A x
        + (v.adicCompletionIntegers F : Set (v.adicCompletion F))ᶜ.indicator
            (fun y => (((LanglandsTunnell.TateLocal.modulus y : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) * B y⁻¹) x
    (∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 → ‖∫ x, a σ x ∂μ‖ ≤ C) ∧
    Tendsto (fun σ : ℝ =>
        (∫ x, (((LanglandsTunnell.TateLocal.modulus x : ℝ≥0) : ℝ) : ℂ) ^ (-(2 * (σ : ℂ) + 1)) * a σ x⁻¹ ∂μ)
          - ∫ x, a σ x ∂μ)
      (𝓝[>] (1 / 2 : ℝ)) (𝓝 0) := by
  revert F v μ m _hm A B _hA _hB
  exact @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion.solution
