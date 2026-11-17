/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul (git blob 5858dedb8546fc2540d7497285aeb4cd40d701f0, sha256 ec27a3154fd4df5bad4767f14bed61d19341cf9be1984fbca25df8105760d473).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_AdelicSpanCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm DihedralWeightOne IsDedekindDomain
open scoped MatrixGroups ModularForm

theorem DihedralWeightOne.exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul
    {M : ℕ} [NeZero M] (h : CuspForm (CongruenceSubgroup.Gamma1 M) 1)
    {N : ℕ} [NeZero N] (ε : DirichletCharacter ℂ N)
    (y : LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h)))
    (hy : y ∈ Submodule.span ℂ (Set.range fun u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ) =>
      (AdelicDock.finEmbed (𝓞 ℚ) ℚ u : AdelicGL2 (𝓞 ℚ) ℚ) •
        LocalNewvector.AdelicSpan.self (weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h))))
    (hK0 : ∀ u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel N), ∀ d : ℤ, IsCoprime d (N : ℤ) →
      (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
          - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel N) →
      ∀ x : AdelicGL2 (𝓞 ℚ) ℚ,
        (LocalNewvector.AdelicSpan.toFn _ y).toFn (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) =
          (ε (d : ZMod N))⁻¹ * (LocalNewvector.AdelicSpan.toFn _ y).toFn x) :
    ∃ F : CuspForm (CongruenceSubgroup.Gamma1 N) 1,
      CuspForm.HasNebentypus ε F ∧
      (LocalNewvector.AdelicSpan.toFn _ y).toFn = weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑F) ∧
      (F = 0 → y = 0) := by
  revert M h N ε y hy hK0
  exact @_root_.P2MW.S_DihedralWeightOne_exists_hasNebentypus_eq_weightOneLift_of_mem_span_of_apply_mul_finEmbed_eq_inv_mul.solution
