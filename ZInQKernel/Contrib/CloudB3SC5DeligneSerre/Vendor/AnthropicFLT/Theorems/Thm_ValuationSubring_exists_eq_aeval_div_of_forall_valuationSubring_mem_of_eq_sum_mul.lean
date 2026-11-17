/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul (git blob 9d7169002fad40dcc60a65837ffd51e0d95d60aa, sha256 750a6e78c1ee071465ccfd3ba4602bca3d39648a07b5e1235bb60049e3de692a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open Polynomial

theorem ValuationSubring.exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F] {f : F} (hf : Transcendental L f)
    {ι : Type*} [Fintype ι] (z : ι → F)
    (hzT : ∀ i, ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → z i ∈ V)
    (hzind : LinearIndependent (IntermediateField.adjoin L ({f} : Set F)) z)
    (hres : ∀ (y : F) (w : ι → F),
      (∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → y ∈ V) →
      (∀ i, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
        ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
        w i * aeval f q = aeval f p) →
      y = ∑ i, w i * z i →
      ∃ (C₁ : ι → L[X]) (μ : ι → F), (∀ i j, (C₁ i).coeff j ∈ A) ∧
        (∀ i, ∃ p q : L[X], (∀ j, A.valuation (p.coeff j) < 1) ∧
          ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
          μ i * aeval f q = aeval f p) ∧
        y = ∑ i, (aeval f (C₁ i) + μ i) * z i)
    (s : F) (w : ι → F)
    (hsT : ∀ V : ValuationSubring F, (∀ c : L, algebraMap L F c ∈ V) → f ∈ V → s ∈ V)
    (hw : ∀ i, ∃ p q : L[X], (∀ j, p.coeff j ∈ A) ∧
      ((∀ j, A.valuation (q.coeff j) ≤ 1) ∧ ∃ d, A.valuation (q.coeff d) = 1) ∧
      w i * aeval f q = aeval f p)
    (hs : s = ∑ i, w i * z i) (i : ι) :
    ∃ p t : L[X], (∀ j, p.coeff j ∈ A) ∧
      (A.valuation (t.coeff 0) = 1 ∧ ∀ j, j ≠ 0 → A.valuation (t.coeff j) < 1) ∧
      w i = aeval f p / aeval f t := by
  revert L A F f hf ι z hzT hzind hres s w hsT hw hs i
  exact @_root_.P2MW.S_ValuationSubring_exists_eq_aeval_div_of_forall_valuationSubring_mem_of_eq_sum_mul.solution
