/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_ComplexPlaceDictionaryOf_exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH (git blob 109bea8bf4b0628b04c5e4b8dc41e02cb2279fd1, sha256 64255a63e57e9ffd55a45b1ad916e372cd19a64843fc2a528e5c237717ab9524).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_ComplexPlaceDictionaryOf_exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open scoped MatrixGroups Topology ModularForm

theorem ModularCurve.ComplexPlaceDictionaryOf.exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (D : ModularCurve.ComplexPlaceDictionaryOf (CohCarrier.GammaH M H) (ModularCurve.xHFunctionField M H))
    (c : UpperHalfPlane →₀ ℤ)
    (hdeg : AlgebraicCurve.Divisor.degree (Finsupp.mapDomain D.pt c) = 0) :
    ∃ ω : UpperHalfPlane → ℂ,
      (∀ γ ∈ CohCarrier.GammaH M H, ω ∣[(2 : ℤ)] γ = ω) ∧
      (∀ σ : SL(2, ℤ), ∃ δ : ℝ, 0 < δ ∧
        (ω ∣[(2 : ℤ)] σ) =O[UpperHalfPlane.atImInfty] fun τ : UpperHalfPlane => Real.exp (-δ * τ.im)) ∧
      ∀ τ : UpperHalfPlane, ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
        (∀ᶠ z in 𝓝[≠] (τ : ℂ), ω (UpperHalfPlane.ofComplex z) =
          (((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) : ℤ) : ℂ) / (z - τ) + g z) ∧
        ((D.ramification τ : ℤ) * Finsupp.mapDomain D.pt c (D.pt τ) = 0 → ω τ = g τ) := by
  revert M H D c hdeg
  exact @_root_.P2MW.S_ModularCurve_ComplexPlaceDictionaryOf_exists_slashInvariant_residue_eq_of_degree_eq_zero_gammaH.solution
