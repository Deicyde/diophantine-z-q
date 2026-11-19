/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq (git blob 6f97d7c45f435f96169abb0bc57317b1a3a93d52, sha256 461fc4bb44645800f9f4d5f3d5d9f2c98497bead5a6d5384022e81cc1efb2514).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_BorelSubgroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicLevel
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_RowIsometryInvariance
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_exists_mem_adelicBorel_mul_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open NumberField NumberField.AdelicLevel AutomorphicForm.WindowedSiegel

theorem AutomorphicForm.exists_mem_adelicBorel_mul_eq
    (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    ∃ b k : AdelicGL2 (𝓞 F) F,
      b ∈ adelicBorel (𝓞 F) F ∧
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) ∧
      g = b * k := by
  revert F g
  exact @_root_.P2MW.S_AutomorphicForm_exists_mem_adelicBorel_mul_eq.solution
