/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry
theorem Algebra.IsStandardSmoothOfRelativeDimension.isDiscreteValuationRing_localization_atPrime
    {k : Type u} [Field k] {A : Type v} [CommRing A] [Algebra k A]
    [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
    (p : Ideal A) [p.IsMaximal] :
    ∃ _ : IsDomain (Localization.AtPrime p), IsDiscreteValuationRing (Localization.AtPrime p) := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime.solution
