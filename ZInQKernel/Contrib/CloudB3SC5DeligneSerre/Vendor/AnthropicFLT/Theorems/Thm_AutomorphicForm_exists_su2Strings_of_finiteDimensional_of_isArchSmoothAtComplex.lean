/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex (git blob b6b413cc43d40594d00000eef700a8a2a0e3ff7f, sha256 8ace1c56cb694de3c0eb4914c47b4f17be848f4d05f1e23bd07d92737b3779c7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion

theorem AutomorphicForm.exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y) :
    ∃ (m : ℕ) (n : Fin m → ℕ) (x : Fin m → ℕ → (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ s p, x s p ∈ Y) ∧
      (∀ s p, n s < p → x s p = 0) ∧
      LinearIndependent ℂ (fun sp : (Σ s : Fin m, Fin (n s + 1)) => x sp.1 sp.2) ∧
      (∀ y ∈ Y, ∃ coef : (s : Fin m) → Fin (n s + 1) → ℂ, y = ∑ s, ∑ p : Fin (n s + 1), coef s p • x s p) ∧
      (∀ s p, archDerivAtComplex hw .iH (x s p) = (Complex.I * ((n s : ℂ) - 2 * (p : ℂ))) • x s p) ∧
      (∀ s p, archDerivAtComplex hw .Fm (x s p) - archDerivAtComplex hw .E (x s p) =
        x s (p + 1) - ((p : ℂ) * ((n s : ℂ) + 1 - (p : ℂ))) • x s (p - 1)) ∧
      (∀ s p, archDerivAtComplex hw .iE (x s p) + archDerivAtComplex hw .iFm (x s p) =
        Complex.I • (x s (p + 1) + ((p : ℂ) * ((n s : ℂ) + 1 - (p : ℂ))) • x s (p - 1))) ∧
      (∀ s p, p ≤ n s → HasCircleWeightAt hw ((n s : ℤ) - 2 * (p : ℤ)) (x s p)) := by
  revert F w hw Y hYs hYK
  exact @_root_.P2MW.S_AutomorphicForm_exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex.solution
