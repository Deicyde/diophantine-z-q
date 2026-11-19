/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental (git blob b99b7ab6cb00eb0fcbcc3635a5b2d973eb1cb035, sha256 b8bb1a04d94837873535b9a6694605f8da85b4a0df20c19ceaf1750be5af1e30).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SmoothedFundamental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false
open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology

theorem ModularCurve.exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ) (Φ : ℂ → ℂ) (S : Finset ℍ) (n : ℍ → ℤ)
    (hloc : ∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z)
    (hinv : ∀ (γ : Γ) (τ : ℍ), Φ (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = Φ τ)
    (hcuspΦ : ∀ σ : SL(2, ℤ), ∃ c : ℂ, c ≠ 0 ∧
      Tendsto (fun τ : ℍ => Φ ((σ • τ : ℍ) : ℂ)) atImInfty (𝓝 c))
    (hdecay : ∀ σ : SL(2, ℤ), Tendsto (fun τ : ℍ =>
      fderiv ℝ (fun u : ℂ => Φ ((σ • ofComplex u : ℍ) : ℂ)) (τ : ℂ)) atImInfty (𝓝 0))
    (hn : ∀ (γ : Γ) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer (Γ) s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) /
      (Nat.card (MulAction.stabilizer (Γ) s) : ℂ) = 0)
    (h : ℝ → ℂ → ℂ)
    (hh : ∀ T z, h T z = (ModularCurve.smoothedFundamental (Γ) T z : ℂ))
    (E : CuspForm (Γ) 2 → ℂ → ℂ)
    (hE : ∀ g z, E g z = ModularCurve.periodAlongOf Γ UpperHalfPlane.I (ofComplex z) g) :
    (∀ (T : ℝ) (g : CuspForm (Γ) 2),
      Integrable fun z : ℂ => E g z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ (h T) z Complex.I - fderiv ℝ Φ z Complex.I * fderiv ℝ (h T) z 1)) ∧
    ∃ Λ ∈ ModularCurve.periodLatticeOf Γ,
      ∀ g : CuspForm (Γ) 2,
        Tendsto (fun T : ℝ =>
          Complex.I / Real.pi * (∫ z : ℂ, E g z / Φ z *
            (fderiv ℝ Φ z 1 * fderiv ℝ (h T) z Complex.I -
              fderiv ℝ Φ z Complex.I * fderiv ℝ (h T) z 1)) +
          2 * ∑ᶠ a : ℂ, ((n (ofComplex a) : ℤ) : ℂ) * E g a * h T a) atTop
          (𝓝 (Λ g + ∑ s ∈ S, 2 * (n s : ℂ) /
            (Nat.card (MulAction.stabilizer (Γ) s) : ℂ) *
              ModularCurve.periodAlongOf Γ UpperHalfPlane.I s g)) := by
  revert Γ hneg Φ S n hloc hinv hcuspΦ hdecay hn hcov hinj hdvd hdeg h hh E hE
  exact @_root_.P2MW.S_ModularCurve_exists_mem_periodLatticeOf_tendsto_windingPairing_smoothedFundamental.solution
