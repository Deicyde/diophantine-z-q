/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place
Modified for the Z-in-Q kernel (2026-11-15, task flt-cqj2): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_FunctionFieldQuadratic
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u
theorem WeierstrassCurve.Affine.FunctionField.addX_addY_specialize_at_place
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] [DecidableEq W.FunctionField]
    (φ₁ φ₂ : W.FunctionField →ₐ[F] W.FunctionField)
    (hcol : ¬ (φ₁ (polyToFunctionField W Polynomial.X) = φ₂ (polyToFunctionField W Polynomial.X) ∧
      φ₁ (yCoord W) = (W.map (algebraMap F W.FunctionField)).toAffine.negY
        (φ₂ (polyToFunctionField W Polynomial.X)) (φ₂ (yCoord W))))
    (hnc : ∀ c : F,
      (W.map (algebraMap F W.FunctionField)).toAffine.addX
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        ≠ algebraMap F W.FunctionField c)
    (v : AlgebraicCurve.Place F W.FunctionField) (Q₁ Q₂ : W.Point)
    (h₁0 : Q₁ = 0 → φ₁ (polyToFunctionField W Polynomial.X) ∉ v.toValuationSubring)
    (h₁s : ∀ (a b : F) (h : W.Nonsingular a b), Q₁ = .some a b h →
      0 < v.ord (φ₁ (polyToFunctionField W Polynomial.X) - algebraMap F W.FunctionField a) ∧
        0 < v.ord (φ₁ (yCoord W) - algebraMap F W.FunctionField b))
    (h₂0 : Q₂ = 0 → φ₂ (polyToFunctionField W Polynomial.X) ∉ v.toValuationSubring)
    (h₂s : ∀ (a b : F) (h : W.Nonsingular a b), Q₂ = .some a b h →
      0 < v.ord (φ₂ (polyToFunctionField W Polynomial.X) - algebraMap F W.FunctionField a) ∧
        0 < v.ord (φ₂ (yCoord W) - algebraMap F W.FunctionField b)) :
    (Q₁ + Q₂ = 0 →
      (W.map (algebraMap F W.FunctionField)).toAffine.addX
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        ∉ v.toValuationSubring) ∧
    (∀ (a b : F) (h : W.Nonsingular a b), Q₁ + Q₂ = .some a b h →
      0 < v.ord ((W.map (algebraMap F W.FunctionField)).toAffine.addX
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        - algebraMap F W.FunctionField a) ∧
      0 < v.ord ((W.map (algebraMap F W.FunctionField)).toAffine.addY
          (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
          (φ₁ (yCoord W))
          ((W.map (algebraMap F W.FunctionField)).toAffine.slope
            (φ₁ (polyToFunctionField W Polynomial.X)) (φ₂ (polyToFunctionField W Polynomial.X))
            (φ₁ (yCoord W)) (φ₂ (yCoord W)))
        - algebraMap F W.FunctionField b)) := by p2m_exact_reverting @_root_.P2MW.S_WeierstrassCurve_Affine_FunctionField_addX_addY_specialize_at_place.solution
