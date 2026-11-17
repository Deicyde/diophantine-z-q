/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt (git blob 6e540491c937cf414ba216e6c877e655ca3919fc, sha256 5a568e1427b27ab9c3cb421c6f9e1a8679dc62c23b0e825d70bda616caea6c21).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

open scoped Classical in

theorem AutomorphicForm.exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (_hv : v ∈ S)
    (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ maximalCompactAt F S) :
    ∃ k' kv : AdelicGL2 (𝓞 F) F,
      k' ∈ maximalCompactAt F (S.erase v) ∧
      kv ∈ maximalCompactAt F {v} ∧ glArch (𝓞 F) F kv = 1 ∧
      k = k' * kv ∧ k' * kv = kv * k' := by
  revert F S v _hv k _hk
  exact @_root_.P2MW.S_AutomorphicForm_exists_mem_maximalCompactAt_erase_mul_eq_of_mem_maximalCompactAt.solution
