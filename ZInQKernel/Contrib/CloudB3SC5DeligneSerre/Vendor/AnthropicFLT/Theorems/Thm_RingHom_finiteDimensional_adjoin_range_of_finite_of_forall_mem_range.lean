/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range (git blob 24e1edc7278cf38e1f237969a7c63d72f1aacd89, sha256 3fa591cdf85292e9e9ba74e61264321b832340d3a92b41a38d82f5f21e1f0edf).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem RingHom.finiteDimensional_adjoin_range_of_finite_of_forall_mem_range
    {R S E K : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    [Field E] [Field K] [Algebra E K]
    (χ' : S →+* K) (h : ∀ r : R, χ' (algebraMap R S r) ∈ (algebraMap E K).range) :
    FiniteDimensional E (IntermediateField.adjoin E (Set.range χ')) := by
  revert R S E K χ' h
  exact @_root_.P2MW.S_RingHom_finiteDimensional_adjoin_range_of_finite_of_forall_mem_range.solution
