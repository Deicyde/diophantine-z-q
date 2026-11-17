/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one (git blob 694cb2bdad889dd96a8e9567551e01329c2e61f6, sha256 32041b1a8cf8710e1f17d5f5432e1d0b4cb17d50530a8123082a962f790354e3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem IsAlgClosed.exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed K]
    (S : Finset E) (hS : (0 : E) ∉ S) :
    ∃ (A : ValuationSubring E) (hK : ∀ c : K, algebraMap K E c ∈ A) (σ : A →+* K),
      RingHom.ker σ = IsLocalRing.maximalIdeal A ∧
      (∀ c : K, σ ⟨algebraMap K E c, hK c⟩ = c) ∧
      ∀ s ∈ S, A.valuation s = 1 := by
  revert K E S hS
  exact @_root_.P2MW.S_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one.solution
