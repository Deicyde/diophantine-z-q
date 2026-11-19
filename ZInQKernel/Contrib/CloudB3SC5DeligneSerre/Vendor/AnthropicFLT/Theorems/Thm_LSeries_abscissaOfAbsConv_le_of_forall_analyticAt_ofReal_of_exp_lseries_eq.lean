/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq (git blob f76cc89ee600033989b03831a02d97bb6cbe202f, sha256 d048702add9a0945fe003f1593f199b7966bd5ca09e024de6a02cbc647c729a7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped ComplexOrder

theorem LSeries.abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq
    (d : ℕ → ℝ) (hd : ∀ n : ℕ, 0 ≤ d n) (Λ : ℂ → ℂ) (x σ₀ : ℝ)
    (han : ∀ σ : ℝ, x < σ → AnalyticAt ℂ Λ (σ : ℂ))
    (heq : ∀ s : ℂ, σ₀ < s.re →
      LSeriesSummable (fun n => (d n : ℂ)) s ∧ Complex.exp (LSeries (fun n => (d n : ℂ)) s) = Λ s) :
    LSeries.abscissaOfAbsConv (fun n => (d n : ℂ)) ≤ (x : EReal) ∧
      ∀ σ : ℝ, x < σ →
        LSeriesSummable (fun n => (d n : ℂ)) σ ∧ Complex.exp (LSeries (fun n => (d n : ℂ)) σ) = Λ σ := by
  revert d hd Λ x σ₀ han heq
  exact @_root_.P2MW.S_LSeries_abscissaOfAbsConv_le_of_forall_analyticAt_ofReal_of_exp_lseries_eq.solution
