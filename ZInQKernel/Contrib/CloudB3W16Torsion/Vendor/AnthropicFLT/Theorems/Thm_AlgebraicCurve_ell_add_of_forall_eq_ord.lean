/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_ell_add_of_forall_eq_ord. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_ell_add_of_forall_eq_ord

set_option backward.isDefEq.respectTransparency false

universe u v

open AlgebraicCurve

theorem AlgebraicCurve.ell_add_of_forall_eq_ord
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] (D : Divisor K F) {P : Divisor K F}
    {f : F} (hf : f ≠ 0) (hP : ∀ v : Place K F, P v = v.ord f) :
    ell (D + P) = ell D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_ell_add_of_forall_eq_ord.solution
