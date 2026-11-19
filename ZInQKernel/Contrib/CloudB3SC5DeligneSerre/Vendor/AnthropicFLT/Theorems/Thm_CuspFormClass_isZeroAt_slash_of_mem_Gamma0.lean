/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CuspFormClass_isZeroAt_slash_of_mem_Gamma0 (git blob 644ffb84e199cd3e62bfc896464141275ba47744, sha256 a45eb70a4dad6904f68d430d87151405aa49bbe775375caa9dff3bb9fafc70a4).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CuspFormClass_isZeroAt_slash_of_mem_Gamma0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups ModularForm

theorem CuspFormClass.isZeroAt_slash_of_mem_Gamma0
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) (σ : CongruenceSubgroup.Gamma0 M)
    {F : Type*} [FunLike F UpperHalfPlane ℂ]
    [CuspFormClass F (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k] (f : F)
    {c : OnePoint ℝ} (hc : IsCusp c (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ))) :
    OnePoint.IsZeroAt c (⇑f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ))) k := by
  revert M H k σ F f c hc
  exact @_root_.P2MW.S_CuspFormClass_isZeroAt_slash_of_mem_Gamma0.solution
