/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_CuspForm_exists_basis_gamma1_two_qCoeff_mem_range_intCast (git blob 04a32d5c765d2f45d18346fcfab910fc16ce07e3, sha256 a2edf03ce3867a01563d3d1dc6c75acbada69a8ccde0cf56db19b6e8b3cba250).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_CuspForm_exists_basis_gamma1_qCoeff_slash_mem_range_intCast

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_CuspForm_exists_basis_gamma1_two_qCoeff_mem_range_intCast

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem solution (M : ℕ) [NeZero M] :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2)),
      ∀ (i : Fin n) (m : ℕ), ModularFormClass.qCoeff (b i) m ∈ Set.range ((↑) : ℤ → ℂ) := by
  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast M 2
  refine ⟨n, b, fun i m => ?_⟩
  simpa using hb i 1 (Subgroup.one_mem _) m
