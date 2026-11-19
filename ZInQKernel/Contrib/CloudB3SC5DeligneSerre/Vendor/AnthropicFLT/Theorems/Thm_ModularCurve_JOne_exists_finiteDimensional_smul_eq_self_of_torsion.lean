/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_JOne_exists_finiteDimensional_smul_eq_self_of_torsion (git blob bd3465848383523a933b27bd92961f31a76875cf, sha256 d50ae4b58df4f15d06a4b54ea1a25a9f5f660ad376f569eb91af272d04817868).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_JOne_exists_finiteDimensional_smul_eq_self_of_torsion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.JOne.exists_finiteDimensional_smul_eq_self_of_torsion (M : ℕ) [NeZero M]
    (n : ℕ) (hn : 0 < n) :
    ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
        ∀ P : ModularCurve.JOne M, (n : ℤ) • P = 0 → σ • P = P := by
  revert M n hn
  exact @_root_.P2MW.S_ModularCurve_JOne_exists_finiteDimensional_smul_eq_self_of_torsion.solution
