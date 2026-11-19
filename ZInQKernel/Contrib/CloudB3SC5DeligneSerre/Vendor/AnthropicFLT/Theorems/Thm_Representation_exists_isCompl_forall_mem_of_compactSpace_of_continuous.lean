/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous (git blob b4a642fc011e0caed1263ad75b4b9395e19b3830, sha256 8bc967ff239262f14a41884bc8c72422fa0e44e77380c72c2c2821bd683c66ce).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v

open MeasureTheory

theorem Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    {E : Type v} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (π : Representation ℂ H E) (hπ : ∀ (ℓ : Module.Dual ℂ E) (v : E), Continuous fun k => ℓ (π k v))
    (P : Submodule ℂ E) (hP : ∀ k : H, ∀ v ∈ P, π k v ∈ P) :
    ∃ Pc : Submodule ℂ E, IsCompl P Pc ∧ ∀ k : H, ∀ v ∈ Pc, π k v ∈ Pc := by
  revert H E π hπ P hP
  exact @_root_.P2MW.S_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous.solution
