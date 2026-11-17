/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer (git blob 8d01222c4e9ac708c7c7bf7c6087d011a2d71052, sha256 f08313f36c84e8e0d3fc47526c9a108b4947987602445adea0dd6fd98b264732).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PeriodOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open UpperHalfPlane
open scoped MatrixGroups Topology

theorem ModularCurve.abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (c : UpperHalfPlane →₀ ℤ)
    (F : UpperHalfPlane → ℂ)
    (hF : ∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ))
    (hΓ : ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ L : ℂ, L ≠ 0 ∧
      Filter.Tendsto (fun τ : UpperHalfPlane => F (σ • τ)) atImInfty (𝓝 L))
    (hord : ∀ τ : UpperHalfPlane, meromorphicOrderAt (fun z : ℂ => F (ofComplex z)) (τ : ℂ) =
      (((Nat.card (MulAction.stabilizer
            (Γ ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) : Subgroup SL(2, ℤ)) τ) / 2 : ℕ) *
        Finsupp.mapDomain (Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane)) c
          (Quotient.mk (MulAction.orbitRel Γ UpperHalfPlane) τ) : ℤ) : WithTop ℤ)) :
    (c.sum fun τ n => n • ModularCurve.periodAlongOf Γ UpperHalfPlane.I τ) ∈
      ModularCurve.periodLatticeOf Γ := by
  revert Γ c F hF hΓ hcusp hord
  exact @_root_.P2MW.S_ModularCurve_abelJacobi_mem_periodLatticeOf_of_meromorphicOrderAt_eq_card_stabilizer.solution
