/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one (git blob db339ba503d36e8e72fccb44cc22d5ea2a61ccc5, sha256 4e6688a9cad2a6dfdd79194d619fa57fab377df5fa5b686cf0a9def136908a3d).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_TateSlots
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open ModularCurve

universe u in

theorem ModularCurve.qTwist_nonToricPoint_of_pow_eq_one
    (K : Type u) [CommRing K] (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : ζ ^ M = 1) (c : Kˣ)
    (j : ℕ) (hj : 0 < j) (hjM : j < M) :
    (qTwist ζ (nonToricPoint K M c j).1, qTwist ζ (nonToricPoint K M c j).2) =
      nonToricPoint K M (c * ζ ^ j) j := by
  revert K M ζ hζ c j hj hjM
  exact @_root_.P2MW.S_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one.solution
