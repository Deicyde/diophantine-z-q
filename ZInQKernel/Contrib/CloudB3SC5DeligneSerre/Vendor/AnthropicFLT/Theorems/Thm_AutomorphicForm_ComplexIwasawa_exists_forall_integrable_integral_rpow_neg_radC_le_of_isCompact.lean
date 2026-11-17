/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact (git blob 773f42941f0567149f864b8896e106f3a33b5edf, sha256 d1503dc8237c5d7e4a0ca5e51c892bc6c750a36491d3decb2a75fb7760a7d732).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ComplexIwasawa
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Topology.Compactness.Compact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory AutomorphicForm.ComplexIwasawa
open scoped ContDiff

theorem AutomorphicForm.ComplexIwasawa.exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact
    (𝒢 : Set (Matrix (Fin 2) (Fin 2) ℂ)) (_h𝒢 : IsCompact 𝒢) (_hdet : ∀ g ∈ 𝒢, g.det ≠ 0)
    (κ₀ κ₁ : ℝ) (_hκ₀ : 2 < κ₀) :
    ∃ M : ℝ, 0 < M ∧ ∀ g ∈ 𝒢, ∀ κ : ℝ, κ₀ ≤ κ → κ ≤ κ₁ →
      Integrable (fun z : ℂ => radC g z ^ (-κ)) ∧ ∫ z : ℂ, radC g z ^ (-κ) ≤ M := by
  revert 𝒢 _h𝒢 _hdet κ₀ κ₁ _hκ₀
  exact @_root_.P2MW.S_AutomorphicForm_ComplexIwasawa_exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact.solution
