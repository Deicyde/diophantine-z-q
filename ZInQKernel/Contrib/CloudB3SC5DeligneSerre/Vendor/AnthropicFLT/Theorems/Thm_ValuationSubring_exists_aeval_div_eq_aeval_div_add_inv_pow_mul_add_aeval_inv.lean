/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv (git blob 452554fd2d7e79b2f51b9183c282bde485d44760, sha256 ea37bf5f1beae715fe09a28028ade158ef6b71639dd9fcba974a28560d311437).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Polynomial

theorem ValuationSubring.exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    (p t : L[X]) (hp : ∀ j, p.coeff j ∈ A)
    (ht : ∃ d, A.valuation (t.coeff d) = 1 ∧ ∀ j, j ≠ d → A.valuation (t.coeff j) < 1)
    (m : ℕ) :
    ∃ p₁ t₁ q s r : L[X],
      (∀ j, p₁.coeff j ∈ A) ∧ (∀ j, q.coeff j ∈ A) ∧ (∀ j, r.coeff j ∈ A) ∧ r.degree < m ∧
      (A.valuation (t₁.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t₁.coeff j) < 1) ∧
      (A.valuation (s.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (s.coeff j) < 1) ∧
      aeval f p / aeval f t =
        aeval f p₁ / aeval f t₁ + (f⁻¹) ^ m * (aeval f⁻¹ q / aeval f⁻¹ s) + aeval f⁻¹ r := by
  revert L A F f hf p t hp ht m
  exact @_root_.P2MW.S_ValuationSubring_exists_aeval_div_eq_aeval_div_add_inv_pow_mul_add_aeval_inv.solution
