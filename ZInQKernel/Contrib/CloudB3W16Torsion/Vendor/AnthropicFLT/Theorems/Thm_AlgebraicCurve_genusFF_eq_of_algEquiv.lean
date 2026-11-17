/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_genusFF_eq_of_algEquiv. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_genusFF_eq_of_algEquiv

set_option backward.isDefEq.respectTransparency false

open AlgebraicCurve

theorem AlgebraicCurve.genusFF_eq_of_algEquiv
    {K F₁ F₂ : Type*} [Field K] [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]
    (e : F₁ ≃ₐ[K] F₂) :
    genusFF K F₁ = genusFF K F₂ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_genusFF_eq_of_algEquiv.solution
