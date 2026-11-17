/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq (git blob 128478abfddb95d8c78dbeff71882f1b2b755d5a, sha256 c744b222a60c35b47669ab14201a03124b13c558ae8acd198c30daf76b6abefa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_AdelicMaximalCompact
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq
    (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (k : AdelicGL2 (𝓞 F) F) (_hk : k ∈ adelicMaximalCompact F) :
    ∃ k₁ k₂ : AdelicGL2 (𝓞 F) F, k₁ ∈ maximalCompactAt F S ∧ k₂ ∈ maximalCompactAway F S ∧ k = k₁ * k₂ := by
  revert F S k _hk
  exact @_root_.P2MW.S_AutomorphicForm_exists_mem_maximalCompactAt_mul_mem_maximalCompactAway_eq.solution
