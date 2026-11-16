/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_StarBank_count
Modification notice (2026-11-15, Cloud Worker 14): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2); mathematical definitions,
theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.FieldTheory.IsAlgClosed.Basic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_StarBank_count

open Polynomial
theorem ModularCurve.StarBank.count {K : Type*} [Field K] [IsAlgClosed K] {p : ℕ}
    (hp0 : (p : K) ≠ 0) (hp2 : 2 ≤ p) {R G : Polynomial K} (hR : R.Monic)
    (hRdeg : R.natDegree = p) (hG : 0 < G.natDegree) {c : K} (hc : c ≠ 0)
    (hdvd : G.comp R ∣ Polynomial.C c * G ^ (p + 1)) :
    ∃ β₀ : K, (∀ β : K, G.IsRoot β → β = β₀) ∧
      R = (Polynomial.X - Polynomial.C β₀) ^ p + Polynomial.C β₀ := by p2m_exact_reverting @_root_.P2MW.S_ModularCurve_StarBank_count.solution
