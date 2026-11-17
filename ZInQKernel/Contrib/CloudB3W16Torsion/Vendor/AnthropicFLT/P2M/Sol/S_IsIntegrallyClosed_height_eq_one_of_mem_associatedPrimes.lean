/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_IsIntegrallyClosed_isDiscreteValuationRing_localization_of_mem_associatedPrimes
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes

theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    {x : B} (hx : x ≠ 0) (P : Ideal B) [P.IsPrime]
    (hP : P ∈ associatedPrimes B (B ⧸ Ideal.span {x})) : P.height = 1 :=
  Ideal.height_eq_one_of_isDiscreteValuationRing_localization_atPrime P
    (IsIntegrallyClosed.isDiscreteValuationRing_localization_of_mem_associatedPrimes hx P hP)
