/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue (git blob 7c257707ac224d8227bcf738d37797fdb952e4c8, sha256 66d8d6ba970f0ce0d290420fb8b541dae1ea57e94f60db96a6b4b91f1453d8db).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped Topology

theorem ModularCurve.exists_meromorphic_logDeriv_eq_of_int_residue
    (m : ℂ → ℤ) (ω : ℂ → ℂ)
    (hres : ∀ a : ℂ, 0 < a.im → ∃ g : ℂ → ℂ, AnalyticAt ℂ g a ∧
      (∀ᶠ z in 𝓝[≠] a, ω z = (m a : ℂ) / (z - a) + g z) ∧ (m a = 0 → ω a = g a)) :
    ∃ G : ℂ → ℂ, ∀ a : ℂ, 0 < a.im →
      MeromorphicAt G a ∧ meromorphicOrderAt G a = (m a : WithTop ℤ) ∧
      (m a ≠ 0 → G a = 0) ∧
      (m a = 0 → AnalyticAt ℂ G a ∧ G a ≠ 0 ∧ HasDerivAt G (ω a * G a) a) := by
  revert m ω hres
  exact @_root_.P2MW.S_ModularCurve_exists_meromorphic_logDeriv_eq_of_int_residue.solution
