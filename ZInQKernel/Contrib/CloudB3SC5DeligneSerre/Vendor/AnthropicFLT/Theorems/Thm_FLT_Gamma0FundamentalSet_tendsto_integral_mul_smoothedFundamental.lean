/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental (git blob e76d0fd40e24f6a907d78bbcb2efbec4c80767f0, sha256 bd67f77f87223f6061044ba81da9947c9ac54e1c3b72b39bf03da532baee92c5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SmoothedFundamental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology

theorem FLT.Gamma0FundamentalSet.tendsto_integral_mul_smoothedFundamental
    {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] (hΓ : (-1 : SL(2, ℤ)) ∈ Γ)
    (P : ℍ → ℂ) (hP : ∀ γ ∈ Γ, ∀ τ : ℍ, P (γ • τ) = P τ)
    (hPm : AEStronglyMeasurable P volume)
    (hPi : IntegrableOn P (FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ) volume) :
    Tendsto (fun T : ℝ => ∫ z : ℂ, P (ofComplex z) *
        ((z.im ^ 2)⁻¹ * ModularCurve.smoothedFundamental Γ T z : ℝ)) atTop
      (𝓝 ((1 / 2 : ℂ) * ∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet Γ, P τ)) := by
  revert Γ hΓ P hP hPm hPi
  exact @_root_.P2MW.S_FLT_Gamma0FundamentalSet_tendsto_integral_mul_smoothedFundamental.solution
