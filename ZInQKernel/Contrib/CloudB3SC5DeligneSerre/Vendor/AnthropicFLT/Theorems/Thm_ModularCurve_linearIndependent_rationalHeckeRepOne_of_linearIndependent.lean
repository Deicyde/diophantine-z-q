/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent (git blob c22c341484260e81e0e4a21516b9d1a4da040555, sha256 645312f5239edae818540c1d3fd84da1b4c0c412d3543dd2b4b9dde2965b515c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.linearIndependent_rationalHeckeRepOne_of_linearIndependent (M p : ℕ) [NeZero M]
    [Fact p.Prime]
    (hin : ModularCurve.HeckeDiamondInputsAll M) (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    {ι : Type} (t : ι → ModularCurve.HeckeAlgOne)
    (hli : letI := ModularCurve.heckeModuleOneBar M
      LinearIndependent ℤ (fun i =>
        Ideal.Quotient.mk (Module.annihilator ModularCurve.HeckeAlgOne (ModularCurve.JOne M)) (t i))) :
    letI := ModularCurve.heckeModuleOneBar M
    LinearIndependent ℚ_[p]
      (fun i => ModularCurve.rationalHeckeRepOne p (ModularCurve.JOne M) (t i)) := by
  revert M p hin hcomm ι t hli
  exact @_root_.P2MW.S_ModularCurve_linearIndependent_rationalHeckeRepOne_of_linearIndependent.solution
