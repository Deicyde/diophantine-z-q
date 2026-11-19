/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isReal (git blob 1b55cb3b82b5d1a1847b5fbe1d5a5004d7748ff6, sha256 a7c89c898d8301985792b96eb3b7e211e2bfc553adfa4dc0b0513de80dbdd715).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isReal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField IsDedekindDomain

open scoped Classical in

theorem NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isReal
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (t : ℝ) :
    NumberField.StandardAddChar.stdAddChar K
        (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t), 0)) =
      Complex.exp (2 * Real.pi * Complex.I * t) := by
  revert K w hw t
  exact @_root_.P2MW.S_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isReal.solution
