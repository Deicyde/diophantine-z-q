/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

theorem Algebra.IsStandardSmooth.exists_isStandardSmoothOfRelativeDimension_of_field
    {k : Type*} [Field k] {B : Type*} [CommRing B] [Algebra k B]
    [Algebra.IsStandardSmooth k B] :
    ∃ n, Algebra.IsStandardSmoothOfRelativeDimension n k B := by p2m_exact_reverting @_root_.P2MW.S_Algebra_IsStandardSmooth_exists_isStandardSmoothOfRelativeDimension_of_field.solution
