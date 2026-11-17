/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DihedralWeightOne_weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero (git blob f45622884edb58f079718edad17376c50b829f49, sha256 5d749e963386270baf14f42cab13f5da44c6696f3cff9e407e6954bc14d77072).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_AdelicSpanCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DihedralWeightOne_weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel AutomorphicForm DihedralWeightOne IsDedekindDomain
open scoped MatrixGroups ModularForm

theorem DihedralWeightOne.weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero
    {M : ℕ} [NeZero M] {ε : DirichletCharacter ℂ M} {h : CuspForm (CongruenceSubgroup.Gamma1 M) 1}
    (hε : CuspForm.HasNebentypus ε h)
    (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) (hu : u ∈ finiteLevelZero (𝓞 ℚ) ℚ (AdelicDock.ratLevel M))
    (d : ℤ)
    (hd : (u : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) 1 1
        - algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (d : ℚ) ∈ idealBall (𝓞 ℚ) ℚ (AdelicDock.ratLevel M))
    (x : AdelicGL2 (𝓞 ℚ) ℚ) :
    weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h) (x * AdelicDock.finEmbed (𝓞 ℚ) ℚ u) =
      (ε (d : ZMod M))⁻¹ * weightOneLift (Ideal.span {(M : 𝓞 ℚ)}) (⇑h) x := by
  revert M ε h hε u hu d hd x
  exact @_root_.P2MW.S_DihedralWeightOne_weightOneLift_mul_finEmbed_eq_inv_nebentypus_mul_of_mem_finiteLevelZero.solution
