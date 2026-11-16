/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Polynomial_mem_range_of_eval_eq_const
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Algebra.Polynomial.Splits
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_Polynomial_mem_range_of_eval_eq_const

theorem Polynomial.mem_range_of_eval_eq_const {F L : Type*} [Field F] [Field L] [Algebra F L] (g : Polynomial F) (x : L) (s : Finset L) (hcard : g.natDegree < s.card) (hval : ∀ y ∈ s, Polynomial.aeval y g = x) : x ∈ (algebraMap F L).range := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_mem_range_of_eval_eq_const.solution
