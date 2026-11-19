/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_of_hasNebentypus_of_qCoeff_hecke_eq (git blob 49a294cbd23a6d243ccc8a901063cad637c67b03, sha256 90bb6abd1a271e4c40a576e291b6304a06fda5874a5414a843cde08b940fee58).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_AdelicSpanCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_of_hasNebentypus_of_qCoeff_hecke_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm DihedralWeightOne IsDedekindDomain
open scoped MatrixGroups ModularForm

theorem DihedralWeightOne.sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_of_hasNebentypus_of_qCoeff_hecke_eq
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
    (hε : CuspForm.HasNebentypus ε h)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (ρ : Fin (ℓ + 1) → GL (Fin 2) ℚ_[ℓ])
    (hρ : ∀ i : Fin (ℓ + 1), ((ρ i : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) =
      if (i : ℕ) < ℓ then !![(1 : ℚ_[ℓ]), ((i : ℕ) : ℚ_[ℓ]); 0, (ℓ : ℚ_[ℓ])]
      else !![(ℓ : ℚ_[ℓ]), 0; 0, 1])
    (lam : ℂ)
    (hT : ∀ n : ℕ,
      ModularFormClass.qCoeff h (ℓ * n) +
          ε (ℓ : ZMod M) * (ℓ : ℂ) ^ ((1 : ℤ) - 1) *
            (if ℓ ∣ n then ModularFormClass.qCoeff h (n / ℓ) else 0) =
        lam * ModularFormClass.qCoeff h n)
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∑ i : Fin (ℓ + 1), weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h) (x * AdelicDock.padicToAdelic ℓ (ρ i)⁻¹) =
      (ε (ℓ : ZMod M))⁻¹ * (ℓ : ℂ) * lam * weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h) x := by
  revert M ε h hε ℓ hℓM ρ hρ lam hT x
  exact @_root_.P2MW.S_DihedralWeightOne_sum_weightOneLift_mul_padicToAdelic_inv_eq_mul_of_hasNebentypus_of_qCoeff_hecke_eq.solution
