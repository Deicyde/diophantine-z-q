/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport (git blob 7294704de766684d3bc5d12edac27ddec606cf86, sha256 33763e6e11d2f8a4a3a2044434adebd39b788d05a9154a4fc5d8fea80c95285f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport
    {E E' V P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace P] {f : E' → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hsupp : HasCompactSupport f)
    {Q : Set P} (hQ : IsCompact Q) {c : P → E'} {ℓ : P → E →L[ℝ] E'}
    (hc : ContinuousOn c Q) (hℓ : ContinuousOn ℓ Q) (hinj : ∀ p ∈ Q, Function.Injective (ℓ p)) :
    (∃ S : Set E, IsCompact S ∧ ∀ p ∈ Q, tsupport (fun x => f (c p + ℓ p x)) ⊆ S) ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ p ∈ Q, ∀ x : E,
      ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun x => f (c p + ℓ p x)) x‖ ≤ C := by
  revert E E' V P f hf hsupp Q hQ c ℓ hc hℓ hinj
  exact @_root_.P2MW.S_exists_isCompact_tsupport_subset_and_norm_pow_mul_norm_iteratedFDeriv_comp_le_of_hasCompactSupport.solution
