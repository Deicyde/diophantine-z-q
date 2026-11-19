/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_slashInvariant_residue_ne_zero_of_pt_ne_gammaH (git blob 86b8aecb67ba21cf69faa5f76d6353001fd9e6a9, sha256 013892b02dacf327d02763d94fba37045e6d22c67a10da42a6645e71699f8744).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_exists_slashInvariant_residue_ne_zero_of_pt_ne_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.ComplexPlaceDictionaryOf.exists_slashInvariant_residue_ne_zero_of_pt_ne_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    {τ₁ τ₂ : ℍ} (hne : D.pt τ₁ ≠ D.pt τ₂) :
    ∃ (ω : ℍ → ℂ) (r : AlgebraicCurve.Place ℂ (ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H)) →₀ ℂ),
      (∀ γ ∈ CohCarrier.GammaH M H, ω ∣[(2 : ℤ)] γ = ω) ∧
      (∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[atImInfty] fun τ : ℍ => Real.exp (-δ * τ.im)) ∧
      r (D.pt τ₁) ≠ 0 ∧
      (∀ P, r P ≠ 0 → P = D.pt τ₁ ∨ P = D.pt τ₂) ∧
      ∀ τ : ℍ, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        ∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (ofComplex z) =
          (D.ramification τ : ℂ) * r (D.pt τ) / (z - τ) + g z := by
  revert M H D τ₁ τ₂ hne
  exact @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_slashInvariant_residue_ne_zero_of_pt_ne_gammaH.solution
