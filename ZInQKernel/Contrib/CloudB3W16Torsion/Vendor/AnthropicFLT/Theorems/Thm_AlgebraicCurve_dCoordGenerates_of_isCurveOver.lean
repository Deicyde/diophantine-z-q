/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_dCoordGenerates_of_isCurveOver. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_dCoordGenerates_of_isCurveOver

set_option backward.isDefEq.respectTransparency false

namespace AlgebraicCurve

theorem dCoordGenerates_of_isCurveOver {K F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :
    ∀ v : Place K F, v.DCoordGenerates := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_dCoordGenerates_of_isCurveOver.solution
