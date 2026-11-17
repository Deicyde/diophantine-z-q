/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate (git blob d3c5c04779629f315937fe544a7de1994d3561ad, sha256 72bd533a644cceee1e9dfab13fc47e4652797c5ba3cd54552444023688b18d1d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicFourier
import Mathlib.Algebra.Module.ZLattice.Summable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open NumberField NumberField.mixedEmbedding
open scoped SchwartzMap Classical

noncomputable section
theorem NumberField.mixedEmbedding.summable_norm_schwartzMap_ringOfIntegers_translate
    (F : Type*) [Field F] [NumberField F]
    (g : 𝓢(NumberField.mixedEmbedding.mixedSpace F, ℂ))
    (x : NumberField.mixedEmbedding.mixedSpace F) :
    Summable fun a : 𝓞 F => ‖g (x + NumberField.mixedEmbedding F (a : F))‖ := by
  revert F g x
  exact @_root_.P2MW.S_NumberField_mixedEmbedding_summable_norm_schwartzMap_ringOfIntegers_translate.solution
