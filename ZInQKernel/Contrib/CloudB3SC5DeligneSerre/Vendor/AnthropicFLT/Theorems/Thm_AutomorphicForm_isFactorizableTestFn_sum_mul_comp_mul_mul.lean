/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_isFactorizableTestFn_sum_mul_comp_mul_mul (git blob 15851fb7fe664550566b0e720c9e3d2f9a37d5ad, sha256 11089143994f84dfdd4646f748415c6fb82f661855b98364e4c3b247e025bfa8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_isFactorizableTestFn_sum_mul_comp_mul_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open MeasureTheory NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.isFactorizableTestFn_sum_mul_comp_mul_mul
    (F : Type) [Field F] [NumberField F]
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) {n : ℕ} (c : Fin n → ℂ)
    (a b : Fin n → AdelicGL2 (𝓞 F) F)
    (ha : ∀ i, a i ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range))
    (hb : ∀ i, b i ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range)) :
    IsFactorizableTestFn F (fun y => ∑ i, c i * f (a i * y * b i)) := by
  revert F f hf n c a b ha hb
  exact @_root_.P2MW.S_AutomorphicForm_isFactorizableTestFn_sum_mul_comp_mul_mul.solution
