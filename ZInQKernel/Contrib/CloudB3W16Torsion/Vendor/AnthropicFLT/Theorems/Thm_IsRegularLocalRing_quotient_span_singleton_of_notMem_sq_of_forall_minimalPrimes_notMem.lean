/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem

set_option backward.isDefEq.respectTransparency false

open IsLocalRing
theorem IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
    (R : Type*) [CommRing R] [IsRegularLocalRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hx2 : x ∉ maximalIdeal R ^ 2)
    (hxmin : ∀ p ∈ minimalPrimes R, x ∉ p) [IsLocalRing (R ⧸ Ideal.span {x})] :
    IsRegularLocalRing (R ⧸ Ideal.span {x}) ∧
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 = (maximalIdeal R).spanFinrank := by p2m_exact_reverting @_root_.P2MW.S_IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem.solution
