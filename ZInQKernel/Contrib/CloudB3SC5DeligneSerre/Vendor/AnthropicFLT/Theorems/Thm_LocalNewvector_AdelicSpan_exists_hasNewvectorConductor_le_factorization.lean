/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LocalNewvector_AdelicSpan_exists_hasNewvectorConductor_le_factorization (git blob 8a8fa6a1363a31467441fffb0841928afca130ba, sha256 7e8ac5e4c16f672a9fc1240bace3f9940101fd3e30b2e7361fdf5f4bef402643).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_AdelicSpanCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LocalNewvector_AdelicSpan_exists_hasNewvectorConductor_le_factorization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem LocalNewvector.AdelicSpan.exists_hasNewvectorConductor_le_factorization
    (φ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → ℂ) (hφ : φ ≠ 0) {N : ℕ} (hN : N ≠ 0)
    (hlev : ∀ g ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ (AdelicDock.ratLevel N),
      ∀ x, φ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ g) = φ x)
    (p : ℕ) [Fact p.Prime] :
    ∃ c : ℕ, c ≤ N.factorization p ∧
      LocalNewvector.HasNewvectorConductor p (LocalNewvector.AdelicSpan φ) c := by
  revert φ hφ N hN hlev p
  exact @_root_.P2MW.S_LocalNewvector_AdelicSpan_exists_hasNewvectorConductor_le_factorization.solution
