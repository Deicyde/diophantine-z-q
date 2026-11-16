/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory AlgebraicGeometry open AlgebraicCurve hiding isCurveOver_of_transcendental

theorem AlgebraicCurve.isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
    {K : Type u} [Field K] [PerfectField K] {F : Type v} [Field F] [Algebra K F]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsIntegral C]
    [SmoothOfRelativeDimension 1 c] (φ : F ≃+* C.functionField)
    (hφ : ∀ a : K, φ (algebraMap K F a) = baseToFunctionField c a) :
    IsCurveOver K F := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one.solution
