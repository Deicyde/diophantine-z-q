/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_periodOf_mul_edgeIntegral (git blob bb68502c01f8343afb7d7446b8bb1adaa41ff9a6, sha256 8e9bbff875e1d083458e3716b07b697e5831072fa2a9dd993a5b2d3f6a90d1e3).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_periodOf_mul_edgeIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.integral_petersson_gammaFundamentalSet_eq_sum_conj_periodOf_mul_edgeIntegral
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    [Fintype (SL(2, ℤ) ⧸ Γ)]
    (k g : CuspForm Γ 2)
    (γT γS : SL(2, ℤ) ⧸ Γ → Γ)
    (hT : ∀ q, ((γT q : Γ) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q)
    (hS : ∀ q, ((γS q : Γ) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q)
    (G : SL(2, ℤ) ⧸ Γ → ℂ → ℂ)
    (hG : ∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
      denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) :
    Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ,
        UpperHalfPlane.petersson 2 k g τ) =
      Complex.I / 2 * ∑ q : SL(2, ℤ) ⧸ Γ,
          conj (ModularCurve.periodOf Γ (γT q) k) *
            (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
        1 / 4 * ∑ q : SL(2, ℤ) ⧸ Γ,
          conj (ModularCurve.periodOf Γ (γS q) k) *
            (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
              G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) := by
  revert Γ hneg k g γT γS hT hS G hG
  exact @_root_.P2MW.S_ModularCurve_integral_petersson_gammaFundamentalSet_eq_sum_conj_periodOf_mul_edgeIntegral.solution
