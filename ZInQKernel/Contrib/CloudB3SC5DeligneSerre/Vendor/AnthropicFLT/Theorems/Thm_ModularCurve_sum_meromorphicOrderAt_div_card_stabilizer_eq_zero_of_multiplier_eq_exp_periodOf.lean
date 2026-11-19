/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp_periodOf (git blob 39221247d43cbbf426e68a9a90362b68c81d4d6c, sha256 0ee1279c8f899c55632dc936a4b32dbbef6eaa530cda32daf3f84111e9945fc4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp_periodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace UpperHalfPlane
end UpperHalfPlane

open _root_.UpperHalfPlane hiding sum_residue_div_card_stabilizer_eq_zero_of_slashInvariant
open scoped MatrixGroups Topology

set_option autoImplicit false

theorem ModularCurve.sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp_periodOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : ℍ => F (σ • τ)) atImInfty (𝓝 L))
    (S : Finset ℍ) (n : ℍ → ℤ)
    (hn : ∀ s ∈ S, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (s : ℂ) = (n s : WithTop ℤ))
    (hinj : ∀ s ∈ S, ∀ t ∈ S,
      (∃ γ : Γ, (γ : SL(2, ℤ)) • s = t) → s = t)
    (hcov : ∀ τ : ℍ, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) ≠ 0 →
      ∃ s ∈ S, ∃ γ : Γ, (γ : SL(2, ℤ)) • s = τ) :
    ∑ s ∈ S, (n s : ℂ) / (Nat.card (MulAction.stabilizer (Γ) s) : ℂ)
      = 0 := by
  revert Γ hneg F k hF hχ hcusp S n hn hinj hcov
  exact @_root_.P2MW.S_ModularCurve_sum_meromorphicOrderAt_div_card_stabilizer_eq_zero_of_multiplier_eq_exp_periodOf.solution
