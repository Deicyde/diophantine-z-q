/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental (git blob e53b4fecaac62ada1f5b9eb6795d3ddbf6e230f0, sha256 add63ef4beeeb796eb5b315caec2e5247adff7c97a5964c82a60d99ba9ae3258).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Polynomial.natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (x : F) (hxL : Transcendental L x) (hx0 : x ≠ 0)
    (f : F) (hint : IsIntegral (Algebra.adjoin L ({x} : Set F)) f) (m : ℕ)
    (h₂ : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → x ∉ V →
      f * (x ^ m)⁻¹ ∈ V)
    (j : ℕ) (c : Polynomial L)
    (hc : Polynomial.aeval x c =
      (((minpoly (Algebra.adjoin L ({x} : Set F)) f).coeff j :
        Algebra.adjoin L ({x} : Set F)) : F)) :
    c.natDegree ≤ ((minpoly (Algebra.adjoin L ({x} : Set F)) f).natDegree - j) * m := by
  revert L F x hxL hx0 f hint m h₂ j c hc
  exact @_root_.P2MW.S_Polynomial_natDegree_aeval_symm_minpoly_adjoin_coeff_le_of_transcendental.solution
