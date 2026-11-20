/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DihedralWeightOne_hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm (git blob 6044d6ba721975ae46c29fa0ab726be34b122707, sha256 f82614ebf18050030a506a8d9f6ab7a26afd1e822b9867a3ff012f254aee588f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_ConductorDatum
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_AdelicSpanCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DihedralWeightOne_hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField AutomorphicForm DihedralWeightOne IsDedekindDomain
open CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem DihedralWeightOne.hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm
    (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf : CuspForm.IsPrimitiveForm ψ f) (q : ℕ) [Fact q.Prime] :
    LocalNewvector.HasNewvectorConductor q
      (LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f)))
      (N.factorization q) := by
  revert N ψ f hf q
  exact @_root_.P2MW.S_DihedralWeightOne_hasNewvectorConductor_adelicSpan_weightOneLift_factorization_of_isPrimitiveForm.solution
