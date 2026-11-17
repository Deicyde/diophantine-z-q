/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AutomorphicForm_SmoothCusp_not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup (git blob aea7d70e7c8892593f59dca564827d0754b95127, sha256 62924f6a2148df0a9d3903520a63d8c3a11e2bd13f943e6a59b55447d28d6c15).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AutomorphicForm_CuspidalConstituent
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AutomorphicForm_SmoothCusp_not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open NumberField.SiegelVolume
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) :
    ¬ SmoothCusp.IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) v φ c := by
  revert F v φ c
  exact @_root_.P2MW.S_AutomorphicForm_SmoothCusp_not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup.solution
