/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j (git blob 6540ea4fee309bb81f7076af19f72ec4ca1cd040, sha256 058a8b0f9b8602247c8272c48e20a00ea6ba68dd6d375d405b372615b93da90b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open WeierstrassCurve WeierstrassCurve.Affine

universe u v in

theorem WeierstrassCurve.exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j
    (K : Type u) [Field K] [IsAlgClosed K] (M : ℕ) [NeZero M] (hM : (M : K) ≠ 0)
    (k Ω : Type v) [Field k] [Field Ω] [DecidableEq Ω] [Algebra K k] [Algebra K Ω] [Algebra k Ω]
    [IsScalarTower K k Ω] [IsAlgClosure k Ω] (E : WeierstrassCurve k) [E.IsElliptic]
    (hE : Transcendental K E.j) (hgen : IntermediateField.adjoin K ({E.j} : Set k) = ⊤) :
    ∃ (P₁ P₂ : (E.baseChange Ω).toAffine.Point) (σ : Ω ≃ₐ[k] Ω) (ε : ℤ),
      M • P₁ = 0 ∧ M • P₂ = 0 ∧
      (∀ a b : ℤ, a • P₁ + b • P₂ = 0 → (M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) ∧
      (ε = 1 ∨ ε = -1) ∧
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₁ = ε • P₁ ∧
      WeierstrassCurve.Affine.Point.map (σ : Ω →ₐ[k] Ω) P₂ = ε • (P₁ + P₂) := by
  revert K M hM k Ω E hE hgen
  exact @_root_.P2MW.S_WeierstrassCurve_exists_algEquiv_map_eq_smul_and_map_eq_smul_add_of_transcendental_j.solution
