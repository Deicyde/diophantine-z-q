/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate (git blob 58b5e1e954d6ad47ca9119806ad3630e45f401d4, sha256 f3f8306cee166844011c647ed9eb8a237bf65489b9a5c5a77812ccc33c06eb9e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (_hN : N ≠ ⊥) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x₀ : AdelicGL2 (𝓞 K) K → ℂ)
    (_hx₀lev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, x₀ (g * k) = x₀ g)
    (r : ℕ) (A : Fin r → AdelicGL2 (𝓞 K) K) (cs : Fin r → ℂ)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (_hxsum : ∀ g, x g = ∑ i, cs i * x₀ (g * A i)) :
    ∃ n : ℕ, 0 < n ∧ ∀ (γ : AdeleRing (𝓞 K) K) (g : AdelicGL2 (𝓞 K) K), γ.1 = 0 →
      (∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → γ.2 v = 0) →
      (∀ v ∈ S, Valued.v (γ.2 v) ≤
        ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) →
      x (g * lowerUnipotentGL2 γ) = x g := by
  revert K N _hN S x₀ _hx₀lev r A cs x _hxsum
  exact @_root_.P2MW.S_AutomorphicForm_exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate.solution
