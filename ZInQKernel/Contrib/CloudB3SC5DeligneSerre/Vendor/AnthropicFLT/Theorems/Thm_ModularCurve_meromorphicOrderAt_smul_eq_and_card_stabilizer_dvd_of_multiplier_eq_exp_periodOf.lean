/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf (git blob 8ec2f1dd7d4d94ba4bcdc976df5d9a1b0a775659, sha256 2b2647f5839fdb65a1f6967d3122db9f6afb38f73ab3f86e97dc214503e7cc0d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

set_option autoImplicit false

theorem ModularCurve.meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    (F : ℍ → ℂ) (k : CuspForm (Γ) 2)
    (hF : ∀ τ : ℍ, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hχ : ∀ (γ : Γ) (τ : ℍ), F ((γ : SL(2, ℤ)) • τ) =
      Complex.exp (2 * Real.pi * Complex.I * ((ModularCurve.periodOf Γ γ k).re : ℂ)) * F τ) :
    (∀ (γ : Γ) (τ : ℍ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (((γ : SL(2, ℤ)) • τ : ℍ) : ℂ) =
        meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ)) ∧
    (∀ (τ : ℍ) (n : ℤ),
      meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) = (n : WithTop ℤ) →
        (Nat.card (MulAction.stabilizer (Γ) τ) : ℤ) ∣ 2 * n) := by
  revert Γ hneg F k hF hχ
  exact @_root_.P2MW.S_ModularCurve_meromorphicOrderAt_smul_eq_and_card_stabilizer_dvd_of_multiplier_eq_exp_periodOf.solution
