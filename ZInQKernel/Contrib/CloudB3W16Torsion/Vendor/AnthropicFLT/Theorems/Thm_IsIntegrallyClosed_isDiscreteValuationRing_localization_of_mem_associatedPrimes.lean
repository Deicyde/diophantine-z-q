/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes

set_option backward.isDefEq.respectTransparency false

theorem IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {x : B} (hx : x ≠ 0) (P : Ideal B) [P.IsPrime]
    (hP : P ∈ associatedPrimes B (B ⧸ Ideal.span {x})) :
    IsDiscreteValuationRing (Localization.AtPrime P) := by p2m_exact_reverting @_root_.P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes.solution
