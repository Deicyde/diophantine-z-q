/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_rep_tateModule_jOne_comm (git blob 0636168615e6a52c6dc6e6d30bdeb46d5ac7f976, sha256 2ed314f29ea80ee0187c091d3c97d6fc53be64d3122caa4f2db2f0ab69199bf2).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_TateModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_JOne_galois_smul_heckeAlgOne_smul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_rep_tateModule_jOne_comm

set_option autoImplicit false

open ModularCurve in

theorem solution (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (T : ModularCurve.HeckeAlgOne)
    (x : TateModule p (ModularCurve.JOne M)) :
    letI := ModularCurve.heckeModuleOneBar M
    TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
        (TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne T x)
      = TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne T
        (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) := by
  letI := ModularCurve.heckeModuleOneBar M
  refine Subtype.ext (funext fun n => ?_)
  rw [TateModule.rep_apply, TateModule.rep_apply, TateModule.rep_apply, TateModule.rep_apply]
  exact ModularCurve.JOne.galois_smul_heckeAlgOne_smul M σ T ((x : ℕ → ModularCurve.JOne M) n)
