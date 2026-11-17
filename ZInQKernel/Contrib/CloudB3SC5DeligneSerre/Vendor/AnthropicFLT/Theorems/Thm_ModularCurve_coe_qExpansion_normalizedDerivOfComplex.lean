/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_coe_qExpansion_normalizedDerivOfComplex (git blob b0cd1ce88c2b1229eda08e706b4ae8d752620245, sha256 e415dd6347a989c9ca2f01013c2d210ac014eafc0ace7887103af14a80a26202).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_QExpansionDiff
import Mathlib.NumberTheory.ModularForms.Derivative
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_coe_qExpansion_normalizedDerivOfComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open UpperHalfPlane Complex Function ModularCurve
open scoped Real Manifold
theorem ModularCurve.coe_qExpansion_normalizedDerivOfComplex (F : ℍ → ℂ) (hper : Function.Periodic (F ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) (hbdd : UpperHalfPlane.IsBoundedAtImInfty F) :
    ((UpperHalfPlane.qExpansion 1 (Derivative.normalizedDerivOfComplex F) : PowerSeries ℂ) :
        LaurentSeries ℂ) =
      ModularCurve.thetaL ℂ
        ((UpperHalfPlane.qExpansion 1 F : PowerSeries ℂ) : LaurentSeries ℂ) := by
  revert F hper hhol hbdd
  exact @_root_.P2MW.S_ModularCurve_coe_qExpansion_normalizedDerivOfComplex.solution
