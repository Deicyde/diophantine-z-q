/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DihedralWeightOne_qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq (git blob 24420864b13316bc3a5c158e19eff5dd98e1b9c7, sha256 d9bbe0e6dca8c3573580e68a81488df2b2d81716455ff2a6e1cd74afb242be8e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_AdelicSpanCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DihedralWeightOne_qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm DihedralWeightOne IsDedekindDomain
open scoped MatrixGroups ModularForm

theorem DihedralWeightOne.qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq
    {N : ℕ} [NeZero N] {ε : DirichletCharacter ℂ N} {F : CuspForm (CongruenceSubgroup.Gamma1 N) 1}
    (hε : CuspForm.HasNebentypus ε F)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (ρ : Fin (ℓ + 1) → GL (Fin 2) ℚ_[ℓ])
    (hρ : ∀ i : Fin (ℓ + 1), ((ρ i : GL (Fin 2) ℚ_[ℓ]) : Matrix (Fin 2) (Fin 2) ℚ_[ℓ]) =
      if (i : ℕ) < ℓ then !![(1 : ℚ_[ℓ]), ((i : ℕ) : ℚ_[ℓ]); 0, (ℓ : ℚ_[ℓ])]
      else !![(ℓ : ℚ_[ℓ]), 0; 0, 1])
    (lam : ℂ)
    (heig : ∀ x : AdelicGL2 (𝓞 ℚ) ℚ, glFin (𝓞 ℚ) ℚ x = 1 →
      LanglandsTunnell.ratArchGL2 x ∈ Matrix.GLPos (Fin 2) ℝ →
        ∑ i : Fin (ℓ + 1), weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) (x * AdelicDock.padicToAdelic ℓ (ρ i)⁻¹) =
          lam * weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) x)
    (n : ℕ) :
    ModularFormClass.qCoeff F (ℓ * n) +
        ε (ℓ : ZMod N) * (ℓ : ℂ) ^ ((1 : ℤ) - 1) *
          (if ℓ ∣ n then ModularFormClass.qCoeff F (n / ℓ) else 0) =
      ε (ℓ : ZMod N) * (ℓ : ℂ)⁻¹ * lam * ModularFormClass.qCoeff F n := by
  revert N ε F hε ℓ hℓN ρ hρ lam heig n
  exact @_root_.P2MW.S_DihedralWeightOne_qCoeff_hecke_eq_of_hasNebentypus_of_sum_weightOneLift_mul_padicToAdelic_inv_eq.solution
