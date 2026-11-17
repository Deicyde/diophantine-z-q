/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WLight_exists_levelFraction_of_stable_family (git blob 07eef2cb215d2fa56c70337c583fb7c82a81000a, sha256 35f2dc45661c37c4a7677505c95f5d387337776e4cdb1d1cbd0eaa795eacb6c8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Mathlib.NumberTheory.ModularForms.Discriminant
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Geometry.Manifold.Notation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WLight_exists_levelFraction_of_stable_family

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.exists_levelFraction_of_stable_family
    (N : ℕ) [NeZero N]
    (L : ℍ → PeriodPair) (hL : ∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1)
    (W : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hW : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), W v τ = ((2 * (Real.pi : ℂ) * Complex.I) ^ 2)⁻¹ *
      PeriodPair.weierstrassP (L τ) ((((v 0).val : ℂ) * (τ : ℂ) + ((v 1).val : ℂ)) / (N : ℂ)))
    (fricke : (Fin 2 → ZMod N) → ℍ → ℂ)
    (hfricke : ∀ (v : Fin 2 → ZMod N) (τ : ℍ), fricke v τ =
      -(ModularForm.E₄ τ * ModularForm.E₆ τ / ModularForm.discriminant τ) / 2592 * W v τ)
    (jf : ℍ → ℂ)
    (hjf : ∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (S : Set (ℍ → ℂ))
    (hhol : ∀ G ∈ S, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hpb : ∀ G ∈ S, ∃ m : ℕ, IsBoundedAtImInfty (G * ModularForm.discriminant ^ m))
    (hst : ∀ (γ : SL(2, ℤ)), ∀ G ∈ S, (G ∘ (γ • ·)) ∈ S)
    (hinv : ∀ G ∈ S, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (γ • τ) = G τ)
    {F : ℍ → ℂ} (hF : F ∈ S) :
    ∃ a b : ℍ → ℂ,
      a ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
      b ∈ Algebra.adjoin ℂ
        (insert jf {g : ℍ → ℂ | ∃ v : Fin 2 → ZMod N, v ≠ 0 ∧ g = fricke v}) ∧
      b ≠ 0 ∧ F * b = a := by
  revert N L hL W hW fricke hfricke jf hjf S hhol hpb hst hinv F hF
  exact @_root_.P2MW.S_WLight_exists_levelFraction_of_stable_family.solution
