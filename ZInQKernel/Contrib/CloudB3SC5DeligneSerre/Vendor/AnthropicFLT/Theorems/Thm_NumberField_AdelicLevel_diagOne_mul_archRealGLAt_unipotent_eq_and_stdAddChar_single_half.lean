/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NumberField_AdelicLevel_diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half (git blob 1d1b274cc8c46e1bd83b598e777eee40362db78e, sha256 6790e5703c796aad9e02811faf6a6eb570e1b3f4ff69dcfc2c1f4f207dc80da1).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_ArchDerivCasimir
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_NumberField_AdelicTraceFin
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_NumberField_AdelicLevel_diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm IsDedekindDomain

open scoped Classical in

theorem NumberField.AdelicLevel.diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half
    (K : Type) [Field K] [NumberField K]
    (w : InfinitePlace K) (hw : w.IsReal) (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : (AdeleRing (𝓞 K) K))).2 = 1) (x : ℝ) :
    diagOne a * archRealGLAt hw (unipotentGL2 x) =
        unipotentGL2 (show (AdeleRing (𝓞 K) K) from (Pi.single w (((a : (AdeleRing (𝓞 K) K))).1 w *
            (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm x), 0)) * diagOne a ∧
      NumberField.StandardAddChar.stdAddChar K
        (show (AdeleRing (𝓞 K) K) from (Pi.single w ((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (1 / 2)), 0)) = -1 := by
  revert K w hw a ha x
  exact @_root_.P2MW.S_NumberField_AdelicLevel_diagOne_mul_archRealGLAt_unipotent_eq_and_stdAddChar_single_half.solution
