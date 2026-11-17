/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_realizeOf_mul_deriv_realizeOf_eq_div_add_gammaH (git blob 351e0497decb693f6ecc16837d0ef87ad6a68c06, sha256 1adb6660d444beb881219491d72ff825cf57ca620a49791b773a329cb153b11c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_exists_realizeOf_mul_deriv_realizeOf_eq_div_add_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.ComplexPlaceDictionaryOf.exists_realizeOf_mul_deriv_realizeOf_eq_div_add_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    [∀ w : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)), w.DCoordGenerates]
    (a x π : ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) (τ : ℍ)
    (η : Ω[(ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H))⁄ℂ])
    (hηax : η = a • KaehlerDifferential.D ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) x)
    (hη : η ≠ 0) (hord : -1 ≤ (D.pt τ).ordDifferential η)
    (hπ : (D.pt τ).ord π = 1)
    (hdπ : (D.pt τ).dCoord = KaehlerDifferential.D ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) π) :
    ∃ (ρ : ℂ) (g : ℂ → ℂ),
      (D.pt τ).differentialCoeff η * π - algebraMap ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) ρ ∈
        (D.pt τ).toValuationSubring.nonunits ∧
      (ρ ≠ 0 ↔ (D.pt τ).ordDifferential η = -1) ∧
      AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝[≠] (τ : ℂ),
        ModularCurve.realizeOf (CohCarrier.GammaH M H) (a : LaurentSeries ℂ) (ofComplex z) *
            deriv (fun w : ℂ => ModularCurve.realizeOf (CohCarrier.GammaH M H) (x : LaurentSeries ℂ) (ofComplex w)) z =
          (D.ramification τ : ℂ) * ρ / (z - τ) + g z := by
  revert M H D a x π τ η hηax hη hord hπ hdπ
  exact @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_realizeOf_mul_deriv_realizeOf_eq_div_add_gammaH.solution
