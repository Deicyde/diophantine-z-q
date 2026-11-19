/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero (git blob c97e76749bc4f5ffff84dc963916ec7f955c32e9, sha256 2580c750ef406c8c82cd48963ebff0a3ee0c2a76f1d6a0e9b52cbd8fbbf76248).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups

set_option autoImplicit false
open Classical in

theorem ModularCurve.sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (Z : (ℍ × ℍ) →₀ ℤ)
    (hZ : ∀ τ : ℍ,
      Z.sum (fun e m =>
        (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.2 = τ then m else 0) -
        (if ∃ γ : Γ, (γ : SL(2, ℤ)) • e.1 = τ then m else 0)) = 0) :
    (Z.sum fun e m => m • ModularCurve.periodAlongOf Γ e.1 e.2) ∈
      ModularCurve.periodLatticeOf Γ := by
  revert Γ Z hZ
  exact @_root_.P2MW.S_ModularCurve_sum_periodAlongOf_mem_periodLatticeOf_of_boundary_eq_zero.solution
