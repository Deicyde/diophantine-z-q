/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_exists_mul_E4_pow_mul_E6_pow_eq_iff (git blob 04276cf1f401b56680910c4d7b76bb0c44a46922, sha256 3e7e08d1129a92cd1de1b5a940fddd7b6f9695e612042f87c47df74ec07bdd38).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_exists_mul_E4_pow_mul_E6_pow_eq_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped Manifold MatrixGroups ModularForm

theorem ModularForm.exists_mul_E4_pow_mul_E6_pow_eq_iff (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (k : ℤ) (a b m : ℕ) (hk : k + 4 * a + 6 * b = 12 * m)
    (F : UpperHalfPlane → ℂ) (hF : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F) :
    (∃ f : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) k, ∀ τ : UpperHalfPlane,
        f τ * (ModularForm.E₄ τ ^ a * ModularForm.E₆ τ ^ b) =
          F τ * ModularForm.discriminant τ ^ m) ↔
      ((∃ G : UpperHalfPlane → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : UpperHalfPlane,
          (F τ * ModularForm.discriminant τ ^ m) ^ 3 = ModularForm.E₄ τ ^ (3 * a) * G τ) ∧
        (∃ G : UpperHalfPlane → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G ∧ ∀ τ : UpperHalfPlane,
          (F τ * ModularForm.discriminant τ ^ m) ^ 2 = ModularForm.E₆ τ ^ (2 * b) * G τ) ∧
        (∀ A : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
          ((F ∘ (A • ·)) * ModularForm.discriminant ^ m)) ∧
        ∀ γ ∈ Γ, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ) := by
  revert Γ k a b m hk F hF
  exact @_root_.P2MW.S_ModularForm_exists_mul_E4_pow_mul_E6_pow_eq_iff.solution
