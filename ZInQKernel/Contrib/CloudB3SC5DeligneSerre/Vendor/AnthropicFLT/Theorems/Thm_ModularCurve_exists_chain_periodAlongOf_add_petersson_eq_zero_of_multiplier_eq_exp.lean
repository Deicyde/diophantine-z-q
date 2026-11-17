/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp (git blob 03a2d95589111dd1f5e315f7d1ac5b03e7c96a8e, sha256 97598975e29443f67b7b23542eb25223f506fdb16cbd206b0c44442a4ae633f8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology

set_option autoImplicit false
open Classical in

theorem ModularCurve.exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L)) :
    ∃ Z : (ℍ × ℍ) →₀ ℤ,
      (∀ τ : ℍ, ∃ n : ℤ,
        meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
          2 * n = (Nat.card (MulAction.stabilizer (Γ) τ) : ℤ) *
            Z.sum (fun e m =>
              (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.2 = τ then m else 0) -
              (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.1 = τ then m else 0))) ∧
      ∀ g : CuspForm (Γ) 2,
        (Z.sum fun e m => m • ModularCurve.periodAlongOf Γ e.1 e.2) g +
          Complex.I * (∫ τ in FLT.Gamma0FundamentalSet.gammaFundamentalSet
            (Γ), UpperHalfPlane.petersson 2 k g τ) = 0 := by
  revert Γ hneg F k hF hχ hcusp
  exact @_root_.P2MW.S_ModularCurve_exists_chain_periodAlongOf_add_petersson_eq_zero_of_multiplier_eq_exp.solution
