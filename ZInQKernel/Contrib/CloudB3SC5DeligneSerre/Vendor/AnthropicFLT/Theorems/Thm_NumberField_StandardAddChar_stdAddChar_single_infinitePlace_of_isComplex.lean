/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isComplex (git blob aa8c7c5cefdaf933a87ab45a53ec62ee93f152bd, sha256 41c219b29b0f00912f5b826852a9bfd1146ca83a308f73e54cb81d37b74c6fee).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField IsDedekindDomain

open scoped Classical in

theorem NumberField.StandardAddChar.stdAddChar_single_infinitePlace_of_isComplex
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsComplex) (z : ℂ) :
    NumberField.StandardAddChar.stdAddChar K
        (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm z), 0)) =
      Complex.exp (2 * Real.pi * Complex.I * ((2 * z.re : ℝ) : ℂ)) := by
  revert K w hw z
  exact @_root_.P2MW.S_NumberField_StandardAddChar_stdAddChar_single_infinitePlace_of_isComplex.solution
