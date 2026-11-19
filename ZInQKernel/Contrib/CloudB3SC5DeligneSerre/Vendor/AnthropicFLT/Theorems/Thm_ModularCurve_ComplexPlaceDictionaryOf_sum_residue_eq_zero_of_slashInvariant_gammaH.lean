/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_sum_residue_eq_zero_of_slashInvariant_gammaH (git blob 259c6c6c5a612098a1c59f9987a775cbc1210c9c, sha256 cc7568c408bc339809c6e69f445e925d01ab895f7949b684b624f8f027a4e586).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_sum_residue_eq_zero_of_slashInvariant_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.ComplexPlaceDictionaryOf.sum_residue_eq_zero_of_slashInvariant_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (ω : ℍ → ℂ) (r : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) →₀ ℂ)
    (hΓ : ∀ γ ∈ CohCarrier.GammaH M H, ω ∣[(2 : ℤ)] γ = ω)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im))
    (hsupp : ∀ P ∈ r.support, ∃ τ : ℍ, D.pt τ = P)
    (hloc : ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) =
          (D.ramification τ : ℂ) * r (D.pt τ) / (z - τ) + g z) :
    r.sum (fun _ a => a) = 0 := by
  revert M H D ω r hΓ hcusp hsupp hloc
  exact @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_sum_residue_eq_zero_of_slashInvariant_gammaH.solution
