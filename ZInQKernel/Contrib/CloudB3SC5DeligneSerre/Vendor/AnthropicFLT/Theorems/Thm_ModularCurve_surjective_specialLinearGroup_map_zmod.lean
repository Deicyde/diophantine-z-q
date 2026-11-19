/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod (git blob 011c1a5e150e2e900687bd91d7c226919af7c770, sha256 52bbca58d62b1b03c19224d24a44b141fb87fa661e06ea9778e9f78725f15b2c).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Data.ZMod.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_surjective_specialLinearGroup_map_zmod

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularCurve.surjective_specialLinearGroup_map_zmod (N : ℕ) [NeZero N] :
    Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N))) := by
  revert N
  exact @_root_.P2MW.S_ModularCurve_surjective_specialLinearGroup_map_zmod.solution
