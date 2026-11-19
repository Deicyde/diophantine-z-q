/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_rep_tateModule_jOne_comm (git blob 906b6eb7c796978f5a1b5f6298da62ecb26796cd, sha256 c82523964b0b534306c94d69ec497ed60721d2ab354a5a0c9fbf98c5d17e546e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_TateModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_rep_tateModule_jOne_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.rep_tateModule_jOne_comm (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (T : ModularCurve.HeckeAlgOne)
    (x : TateModule p (ModularCurve.JOne M)) :
    letI := ModularCurve.heckeModuleOneBar M
    TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
        (TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne T x)
      = TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne T
        (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) := by
  revert M p hcomm σ T x
  exact @_root_.P2MW.S_ModularCurve_rep_tateModule_jOne_comm.solution
