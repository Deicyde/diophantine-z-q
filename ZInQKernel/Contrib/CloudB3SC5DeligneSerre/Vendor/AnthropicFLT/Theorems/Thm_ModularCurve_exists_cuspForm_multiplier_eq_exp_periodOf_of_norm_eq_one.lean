/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one (git blob 40be0442c596162de0e2bf7d9b9d822b4eacbad3, sha256 706d73b5f2771e32563dee0f8e594b44969148a800c6622c6f3600156c4791b5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology
open Classical in

theorem ModularCurve.exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (hΓ : CongruenceSubgroup.IsCongruenceSubgroup Γ) (c : UpperHalfPlane →₀ ℤ)
    (F : ℍ → ℂ) (χ : Γ → ℂ)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) = χ γ * F τ)
    (hunit : ∀ γ : Γ, ‖χ γ‖ = 1)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : ℍ, ∃ n : ℤ,
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) ∧
        2 * n = (Nat.card (MulAction.stabilizer Γ τ) : ℤ) *
          c.sum (fun τ' m =>
            if ∃ γ : Γ, (γ : SL(2, ℤ)) • τ' = τ then m else 0)) :
    ∃ k : CuspForm Γ 2, ∀ γ : Γ,
      χ γ = Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) := by
  revert Γ hneg hΓ c F χ hF hχ hunit hcusp hord
  exact @_root_.P2MW.S_ModularCurve_exists_cuspForm_multiplier_eq_exp_periodOf_of_norm_eq_one.solution
