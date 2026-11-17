/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero (git blob 9c6a9c6738fdcd6154be9982e17d5d0a04e9cbe3, sha256 de013549512b52733bc83079baec07a1eb63783643f35125b6500a326ae1c0bb).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

universe u v in

theorem WeierstrassCurve.exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero
    {F : Type u} {Ω : Type v} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic F Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] (h3 : (3 : F) ≠ 0) :
    ∃ S : IntermediateField F Ω, FiniteDimensional F S ∧ IsGalois F S ∧
      ∀ (M : IntermediateField F Ω), S ≤ M →
      ∀ (A : ValuationSubring M), IsUnit (3 : A) → algebraMap F M E.j ∈ A →
      ∃ (W : WeierstrassCurve A) (κ : VariableChange M),
        κ • E.baseChange M = W.map A.subtype ∧ IsUnit W.Δ ∧
        ∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (∀ P : (E.baseChange M).toAffine.Point, 3 • P = 0 →
              Point.map (σ : M →ₐ[F] M) P = P) →
          (∃ g : VariableChange A, g.map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
              g.map (residue A) = 1) →
          ∀ x : M, (x : Ω) ∈ S → σ x = x := by
  revert F Ω E h3
  exact @_root_.P2MW.S_WeierstrassCurve_exists_isGalois_goodModel_inertia_faithful_of_three_ne_zero.solution
