/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq (git blob 239821708811b2bebca689022dc55ace3e132147, sha256 2f2ae7ad2b7d9dcf6cba5fc97d3d6591e5160bf2ead7e09f0f121feb6f27b68a).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_TateGlobalZeta
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open NumberField NumberField.TateGlobal
open scoped NNReal

theorem NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq
    (F : Type) [Field F] [NumberField F] :
    ∃ s : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ, Continuous s ∧
      (∀ r : ℝ≥0ˣ, ideleNorm F (s r) = ((r : ℝ≥0) : ℝ)) ∧
      ∀ r : ℝ≥0ˣ, ((s r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
  revert F
  exact @_root_.P2MW.S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.solution
