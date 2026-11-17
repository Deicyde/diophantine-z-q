/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_cechDiff_baseChange_of_isAlgClosed. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_cechDiff_baseChange_of_isAlgClosed

set_option backward.isDefEq.respectTransparency false

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
theorem AlgebraicGeometry.Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed
    {R : Type u} [CommRing R] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover)
    (c : C ⟶ Spec (CommRingCat.of R)) (K : Type u) [Field K] [IsAlgClosed K] [Algebra R K]
    [IsIntegral (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K))]
    [IsProper (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))]
    [SmoothOfRelativeDimension 1 (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))] :
    letI := (AlgebraicCurve.baseToFunctionField
      (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))).toAlgebra
    Module.Finite K (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange K)) ∧
      Module.finrank K (LinearMap.ker ((𝒱.structureSheafSections c).cechDiff.baseChange K)) = 1 ∧
      Module.finrank K ((K ⊗[R] (𝒱.cover c).A01) ⧸
          LinearMap.range ((𝒱.structureSheafSections c).cechDiff.baseChange K)) =
        AlgebraicCurve.genusFF K (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R K)).functionField := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_cechDiff_baseChange_of_isAlgClosed.solution
