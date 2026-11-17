/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_moduleFinite_and_free_padicInt_tateModule_jH (git blob b22fcd4112042e9f3d3f1ce0773e033d3b4e3614, sha256 b9d0e08ec1bf7428232f537c7703edd1f12ebbc3bc77153976b66c8a2556327e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_moduleFinite_and_free_padicInt_tateModule_jH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH (M p : ℕ) [NeZero M] [Fact p.Prime]
    (H : Subgroup (ZMod M)ˣ) :
    Module.Finite ℤ_[p] (TateModule p (ModularCurve.JH M H)) ∧
      Module.Free ℤ_[p] (TateModule p (ModularCurve.JH M H)) := by
  revert M p H
  exact @_root_.P2MW.S_ModularCurve_moduleFinite_and_free_padicInt_tateModule_jH.solution
