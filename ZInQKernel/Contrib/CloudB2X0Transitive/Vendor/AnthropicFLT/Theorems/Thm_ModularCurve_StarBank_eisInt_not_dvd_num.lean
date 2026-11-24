/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_StarBank_eisInt_not_dvd_num
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_StarBank_eisInt_not_dvd_num

open scoped ArithmeticFunction.sigma
open Finset
theorem ModularCurve.StarBank.eisInt_not_dvd_num {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ¬ (ℓ : ℤ) ∣ (bernoulli (ℓ - 1)).num := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_StarBank_eisInt_not_dvd_num.solution
