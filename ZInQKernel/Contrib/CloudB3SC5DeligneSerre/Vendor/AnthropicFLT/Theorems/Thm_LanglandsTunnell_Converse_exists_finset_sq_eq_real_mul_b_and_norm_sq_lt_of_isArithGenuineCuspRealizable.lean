/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable (git blob 2b561843977f9482954ae850bb904e1bef8a5fde, sha256 10bca95c28df9184bd757984dfd2bcaaff537bc8326141981b1f342777feec72).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

theorem LanglandsTunnell.Converse.exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable
    (Φ : AutomorphicForm.HeckeEigensystem ℚ ℂ)
    (hΦ : AutomorphicForm.IsArithGenuineCuspRealizable ℚ (AutomorphicForm.productionPinsGeneral ℚ) Φ) :
    ∃ S : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)),
      ∀ p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ), p ∉ S →
        (∃ t : ℝ, 0 ≤ t ∧ Φ.a p ^ 2 = (t : ℂ) * Φ.b p) ∧
        ‖Φ.a p‖ ^ 2 <
          ‖Φ.b p‖ * (((Ideal.absNorm p.asIdeal : ℕ) : ℝ) + 2 + ((Ideal.absNorm p.asIdeal : ℕ) : ℝ)⁻¹) := by
  revert Φ hΦ
  exact @_root_.P2MW.S_LanglandsTunnell_Converse_exists_finset_sq_eq_real_mul_b_and_norm_sq_lt_of_isArithGenuineCuspRealizable.solution
