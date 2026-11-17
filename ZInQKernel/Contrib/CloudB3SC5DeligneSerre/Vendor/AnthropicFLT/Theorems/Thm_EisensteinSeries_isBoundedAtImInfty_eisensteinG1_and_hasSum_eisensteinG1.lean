/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1 (git blob e07b32e86182b6dd802c6e5f8999eb0b8e39054a, sha256 8c2929f2d1eab66d9f62f75f3e7da5e9420daae9bf8646a9cc2805f6c0a9dc48).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EisensteinSeries_WeierstrassZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped Real

theorem EisensteinSeries.isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1 (N : ℕ) [NeZero N] :
    (∀ v : Fin 2 → ℤ, (¬ ∀ i, (N : ℤ) ∣ v i) →
        UpperHalfPlane.IsBoundedAtImInfty (EisensteinSeries.eisensteinG1 N v)) ∧
    (∀ (b : ℤ), ¬ (N : ℤ) ∣ b → ∀ τ : UpperHalfPlane,
        HasSum (fun n : ℕ => (if n = 0 then π / N * Complex.cot (π * b / N) else
            -(2 * π * Complex.I) / N * ∑ k ∈ n.divisors,
              (Complex.exp (2 * π * Complex.I * b * k / N) -
                Complex.exp (-(2 * π * Complex.I * b * k / N)))) *
            Complex.exp (2 * π * Complex.I * τ) ^ n)
          (EisensteinSeries.eisensteinG1 N ![0, b] τ)) := by
  revert N
  exact @_root_.P2MW.S_EisensteinSeries_isBoundedAtImInfty_eisensteinG1_and_hasSum_eisensteinG1.solution
