/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map (git blob 148c91a97e7cf226e0d6141c46c8709e4150ca6b, sha256 65365ea8b37d155a0906833d7dd5e45d2e197104dce5777a66a3e087a981532a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_WeierstrassCurve_VariableChangePointEquiv
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing

universe u v in

theorem WeierstrassCurve.exists_inertia_equivariant_reduction_of_variableChange_eq_map
    {F : Type u} {M : Type v} [Field F] [Field M] [DecidableEq M] [Algebra F M]
    (A : ValuationSubring M) [DecidableEq (ResidueField A)]
    (E : WeierstrassCurve F) (W : WeierstrassCurve A) (κ : VariableChange M)
    (hκ : κ • E.baseChange M = W.map A.subtype) (hΔ : IsUnit W.Δ) :
    ∃ (θ : (E.baseChange M).toAffine.Point →+ (W.map (residue A)).toAffine.Point)
      (g : (M ≃ₐ[F] M) → VariableChange A),
      (∀ (n : ℕ) (P : (E.baseChange M).toAffine.Point),
          (n : ResidueField A) ≠ 0 → n • P = 0 → θ P = 0 → P = 0) ∧
      (∀ (σ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (g σ).map A.subtype = κ * (κ.map (σ : M →+* M))⁻¹ ∧
          (g σ).map (residue A) • W.map (residue A) = W.map (residue A) ∧
          ∀ P : (E.baseChange M).toAffine.Point,
            HEq (Point.vcInvFun ((g σ).map (residue A)) (W.map (residue A)).toAffine (θ P))
              (θ (Point.map (σ : M →ₐ[F] M) P))) ∧
      (∀ (σ τ : M ≃ₐ[F] M) (hσ : σ ∈ A.decompositionSubgroup F)
          (hτ : τ ∈ A.decompositionSubgroup F),
          (⟨σ, hσ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (⟨τ, hτ⟩ : A.decompositionSubgroup F) ∈ A.inertiaSubgroup F →
          (g (σ * τ)).map (residue A) = (g σ).map (residue A) * (g τ).map (residue A)) := by
  revert F M A E W κ hκ hΔ
  exact @_root_.P2MW.S_WeierstrassCurve_exists_inertia_equivariant_reduction_of_variableChange_eq_map.solution
