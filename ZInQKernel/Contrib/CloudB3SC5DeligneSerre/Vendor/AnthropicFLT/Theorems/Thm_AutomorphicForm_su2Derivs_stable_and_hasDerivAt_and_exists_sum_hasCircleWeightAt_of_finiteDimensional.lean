/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional (git blob 7830a73c7a69e501f51a3cad7f58ed50ffdd8537, sha256 ffa038c2532b73058cc2cf8ec83ebe36fb67ea0a437079e7a82e5f6e60d4d76a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y) :
    let D₀ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) := fun y => archDerivAtComplex hw .iH y
    let D₁ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) :=
      fun y => archDerivAtComplex hw .Fm y - archDerivAtComplex hw .E y
    let D₂ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) :=
      fun y => archDerivAtComplex hw .iE y + archDerivAtComplex hw .iFm y
    let Mrot : ℝ → AdelicGL2 (𝓞 F) F := fun s => archFlowAtComplex hw .iH s
    let Rrot : ℝ → AdelicGL2 (𝓞 F) F := fun s => archComplexLiftAt hw
      !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]
    let Srot : ℝ → AdelicGL2 (𝓞 F) F := fun s => archComplexLiftAt hw
      !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]
    (∀ y ∈ Y, D₀ y ∈ Y ∧ D₁ y ∈ Y ∧ D₂ y ∈ Y) ∧
    (∀ y ∈ Y, ∀ (g : AdelicGL2 (𝓞 F) F) (s : ℝ),
      HasDerivAt (fun t : ℝ => y (g * Mrot t)) (D₀ y (g * Mrot s)) s ∧
      HasDerivAt (fun t : ℝ => y (g * Rrot t)) (D₁ y (g * Rrot s)) s ∧
      HasDerivAt (fun t : ℝ => y (g * Srot t)) (D₂ y (g * Srot s)) s) ∧
    (∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S ≤ Y →
      (∀ y ∈ S, D₀ y ∈ S ∧ D₁ y ∈ S ∧ D₂ y ∈ S) →
      ∀ y ∈ S, ∀ s : ℝ, (fun g => y (g * Mrot s)) ∈ S ∧ (fun g => y (g * Rrot s)) ∈ S ∧
        (fun g => y (g * Srot s)) ∈ S) ∧
    (∀ y ∈ Y, ∃ (ms : Finset ℤ) (ys : ℤ → (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ m ∈ ms, ys m ∈ Y ∧ HasCircleWeightAt hw m (ys m) ∧ D₀ (ys m) = (Complex.I * (m : ℂ)) • ys m) ∧
      y = ∑ m ∈ ms, ys m) := by
  revert F w hw Y hYs hYK
  exact @_root_.P2MW.S_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional.solution
