/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_heckeDiamondCommuteBar (git blob 323cbe2a9a9fb685cb17d7937f413e94ca87f4df, sha256 5819c260e3d0caba4488a4bcced619738ca98decd15228e517e3796883e4605b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1HeckeModule
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_heckeOperatorOneBar_comm
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_heckeOperatorOneBar_comm_diamondOneBar
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_diamondOneBar_comm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_heckeDiamondCommuteBar

set_option autoImplicit false

open ModularCurve

theorem solution (M : ℕ) [NeZero M] :
    ModularCurve.HeckeDiamondCommuteBar M := by
  intro i j
  rcases i with ℓ | d <;> rcases j with ℓ' | e
  · rw [heckeDiamondGenBar_inl, heckeDiamondGenBar_inl]
    exact heckeOperatorOneBar_comm M ℓ ℓ'
  · rw [heckeDiamondGenBar_inl, heckeDiamondGenBar_inr]
    exact heckeOperatorOneBar_comm_diamondOneBar M ℓ e
  · rw [heckeDiamondGenBar_inl, heckeDiamondGenBar_inr]
    exact (heckeOperatorOneBar_comm_diamondOneBar M ℓ' d).symm
  · rw [heckeDiamondGenBar_inr, heckeDiamondGenBar_inr]
    exact diamondOneBar_comm M d e
