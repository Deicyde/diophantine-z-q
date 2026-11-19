/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CohCarrier_index_gammaH_eq_index_gamma0_mul_index (git blob 969429e0e56ff12491bd4601a7a4e84c46ecbf58, sha256 283034f9b9e56ee20d148fabbb3bdfbc8e799003a3d0db8b30bee5546f10a528).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_CohCarrier_index_gammaH_eq_index_gamma0_mul_index

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open scoped MatrixGroups in

theorem CohCarrier.index_gammaH_eq_index_gamma0_mul_index (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).index = (CongruenceSubgroup.Gamma0 M).index * H.index := by
  revert M H
  exact @_root_.P2MW.S_CohCarrier_index_gammaH_eq_index_gamma0_mul_index.solution
