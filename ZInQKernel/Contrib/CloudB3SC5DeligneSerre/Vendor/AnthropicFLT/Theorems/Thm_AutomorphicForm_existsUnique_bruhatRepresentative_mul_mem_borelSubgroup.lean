/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_existsUnique_bruhatRepresentative_mul_mem_borelSubgroup (git blob 3b196ded7f574b216fdf96c55628ad34959d0790, sha256 a423140b6a80f3695d4d8622ebc0c58b0030e3075bc8c2a10203c0a8c589d56a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BorelSubgroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_WeylIntertwining
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_existsUnique_bruhatRepresentative_mul_mem_borelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.existsUnique_bruhatRepresentative_mul_mem_borelSubgroup
    (K : Type*) [Field K] (γ : GL (Fin 2) K) :
    ∃! o : Option K, (o.elim 1 fun ξ => (gl2Weyl : GL (Fin 2) K) * unipotentGL2 ξ) * γ ∈ borelSubgroup K := by
  revert K γ
  exact @_root_.P2MW.S_AutomorphicForm_existsUnique_bruhatRepresentative_mul_mem_borelSubgroup.solution
