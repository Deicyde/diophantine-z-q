/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Polynomial_irreducible_of_transitive_ringAut
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Algebra.Polynomial.Splits
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_Polynomial_irreducible_of_transitive_ringAut

theorem Polynomial.irreducible_of_transitive_ringAut {F L : Type*} [Field F] [Field L] [Algebra F L] (P : Polynomial F) (hP : P.Monic) (hPs : (P.map (algebraMap F L)).Splits) (σ : L ≃+* L) (hσ : ∀ a : F, σ (algebraMap F L a) = algebraMap F L a) (y₀ : L) (r : ℕ → L) (n : ℕ) (hroots : (P.map (algebraMap F L)).roots = y₀ ::ₘ (Multiset.range n).map r) (hnodup : (P.map (algebraMap F L)).roots.Nodup) (hcycle : ∀ i < n, σ (r i) = r ((i + 1) % n)) (hy₀ : y₀ ∉ (algebraMap F L).range) : Irreducible P := by p2m_exact_reverting @_root_.P2MW.S_Polynomial_irreducible_of_transitive_ringAut.solution
