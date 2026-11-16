/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions
attribute [-simp] WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap

open AlgebraicCurve

universe u
theorem WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq
    {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]
    (E : WeierstrassCurve K) [E.IsElliptic]
    (ι : E.toAffine.FunctionField →ₐ[K] E.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) :
    ∃ (K₀ : IntermediateField ℚ K), Countable K₀ ∧
      ∃ (E₀ : WeierstrassCurve K₀), E₀.IsElliptic ∧ E₀.map (algebraMap K₀ K) = E ∧
        ∃ (ι₀ : (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField →ₐ[AlgebraicClosure K₀]
            (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField),
          ι₀.toRingHom.IsIntegral ∧
          ∃ (hfin₀ : FiniteAlong (AlgebraicClosure K₀) ι₀),
            finrankAlong (AlgebraicClosure K₀) ι₀ = finrankAlong K ι := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.solution
