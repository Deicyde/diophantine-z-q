/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex (git blob 3d5585357d565f2b30343213a4875e0491790102, sha256 3c266ec5a0408ec8a6fcd18707e80672603164a6c9ae72a330473a46610f0730).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_SmoothedFundamental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open UpperHalfPlane MeasureTheory Filter
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ (γ : Γ) (τ : ℍ), n ((γ : SL(2, ℤ)) • τ) = n τ)
    (hcov : ∀ τ : ℍ, n τ ≠ 0 → ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ)
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hdvd : ∀ s ∈ S, (Nat.card (MulAction.stabilizer Γ s) : ℤ) ∣ 2 * n s)
    (hdeg : ∑ s ∈ S, (n s : ℂ) /
      (Nat.card (MulAction.stabilizer Γ s) : ℂ) = 0) :
    ∃ (V : ℂ → ℂ) (b : ℍ) (m : ℍ → ℤ) (F : ℍ → ℂ → ℂ),
      (∀ (γ : Γ) (τ : ℍ), V (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) = V τ) ∧
      (∀ τ : ℍ, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ (τ : ℂ) ∧ Ψ τ ≠ 0 ∧
        V =ᶠ[𝓝 (τ : ℂ)] fun z => (z - τ) ^ (n τ) * Ψ z) ∧
      (∀ σ : SL(2, ℤ), ∃ Y : ℝ, ∀ z : ℂ, Y < z.im → V ((σ • ofComplex z : ℍ) : ℂ) = 1) ∧
      (∀ s ∈ S, Continuous (F s) ∧ HasCompactSupport (F s) ∧ tsupport (F s) ⊆ {z : ℂ | 0 < z.im} ∧
        ∀ E E' : ℂ → ℂ, (∀ z : ℂ, 0 < z.im → HasDerivAt E (E' z) z) →
          Integrable (fun z : ℂ => E' z * F s z) ∧
            ∫ z : ℂ, E' z * F s z = Real.pi * (E s - E b)) ∧
      (∀ s ∈ S, (Nat.card (MulAction.stabilizer Γ s) : ℤ) * m s =
        2 * n s) ∧
      ∀ᵐ z : ℂ, 0 < z.im →
        (fderiv ℝ V z 1 + Complex.I * fderiv ℝ V z Complex.I) / 2 / V z =
          ∑ s ∈ S, (m s : ℂ) / 2 * ∑ᶠ γ : Γ,
            F s (((γ : SL(2, ℤ)) • ofComplex z : ℍ) : ℂ) *
              conj (1 / denom ((γ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) := by
  revert Γ hneg S n hn hcov hinj hdvd hdeg
  exact @_root_.P2MW.S_ModularCurve_exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex.solution
