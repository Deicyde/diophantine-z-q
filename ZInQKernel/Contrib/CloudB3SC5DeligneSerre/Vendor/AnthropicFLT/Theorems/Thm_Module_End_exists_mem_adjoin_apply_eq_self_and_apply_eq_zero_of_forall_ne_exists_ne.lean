/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Module_End_exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne (git blob 7c2ca084fcb7aee8c9a630763ca8893c878c02ea, sha256 8e87555cd11412391f6eef65bc5357ea8e39ed6399de1d505f5a93e2109ef0b1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Module_End_exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem Module.End.exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne
    {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (W : ι → Submodule K V) (𝒯 : Set (Module.End K V)) (c : Module.End K V → ι → K)
    (hT : ∀ T ∈ 𝒯, ∀ (i : ι), ∀ v ∈ W i, T v = c T i • v)
    (hsep : ∀ i j : ι, i ≠ j → ∃ T ∈ 𝒯, c T i ≠ c T j) (i : ι) :
    ∃ e ∈ Algebra.adjoin K 𝒯, (∀ v ∈ W i, e v = v) ∧ ∀ j : ι, j ≠ i → ∀ v ∈ W j, e v = 0 := by
  revert K V ι W 𝒯 c hT hsep i
  exact @_root_.P2MW.S_Module_End_exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne.solution
