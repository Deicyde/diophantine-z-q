/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod (git blob c3876e1a6b58c9f1dc91795ad30213c56c5c7fb1, sha256 ea124500a84bd351106dec9a3b7dbaaba6a256e45bef8193702bf8e53880593a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.InfinitePlace

open scoped Classical in

theorem AutomorphicForm.LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod
    (F : Type) [Field F] [NumberField F]
    (kdat : {w : InfinitePlace F // w.IsReal} → ℤ)
    (abm : {w : InfinitePlace F // w.IsComplex} → ℕ × ℕ × ℕ)
    (_habm : ∀ w, (abm w).1 + (abm w).2.1 ≤ (abm w).2.2) :
    ∃ C : ℝ, ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 →
      ‖∫ y : mixedEmbedding.mixedSpace F,
          (∏ i : {w : InfinitePlace F // w.IsReal},
              ((((y.1 i : ℝ) : ℂ) - Complex.I) / ((Real.sqrt (1 + (y.1 i) ^ 2) : ℝ) : ℂ)) ^ (kdat i)
                * (((1 + (y.1 i) ^ 2 : ℝ) : ℂ)) ^ (-((σ : ℂ) + 1 / 2)))
          * (∏ w : {w : InfinitePlace F // w.IsComplex},
              (y.2 w) ^ (abm w).1 * (starRingEnd ℂ) (y.2 w) ^ (abm w).2.1
                * (((1 + ‖y.2 w‖ ^ 2 : ℝ) : ℂ)) ^ (-(2 * (σ : ℂ) + 1) - ((abm w).2.2 : ℂ) / 2))‖ ≤ C := by
  revert F kdat abm _habm
  exact @_root_.P2MW.S_AutomorphicForm_LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod.solution
