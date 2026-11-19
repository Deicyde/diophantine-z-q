/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_DihedralWeightOne_factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1 (git blob 4d15265bfb772ef1dc73aa60e1109027d143d274, sha256 b14340c148fbeef573e88bf5fdbd4aef5e360b1b35039d44c2c217290c49c3f6).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_DihedralWeightOneLift
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_ConductorDatum
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_LocalNewvector_AdelicSpanCarrier
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CuspForm_PrimitiveFormGamma1
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AdelicDock_LocalEmbedding
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_DihedralWeightOne_factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField AutomorphicForm DihedralWeightOne IsDedekindDomain
open CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem DihedralWeightOne.factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1
    (N : ℕ) [NeZero N] (ψ : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf : CuspForm.IsPrimitiveForm ψ f) (q : ℕ) [Fact q.Prime] (m : ℕ)
    (y : LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f)))
    (hy : y ∈ Submodule.span ℂ
      (Set.range fun x : GL (Fin 2) ℚ_[q] =>
        x • LocalNewvector.AdelicSpan.self (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f))))
    (hfix : y ∈ LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 q m)
      (LocalNewvector.AdelicSpan (weightOneLift (Ideal.span {(N : 𝓞 ℚ)}) (⇑f))))
    (hy0 : y ≠ 0) :
    N.factorization q ≤ m := by
  revert N ψ f hf q m y hy hfix hy0
  exact @_root_.P2MW.S_DihedralWeightOne_factorization_le_of_mem_span_weightOneLift_of_mem_fixedSubmodule_padicK1.solution
