/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularForm_isBoundedAtImInfty_heckeU (git blob 466cbf94dced4b7d796f1dcadc377ea751eeec0c, sha256 519aa9fd4543875160681388f5bde02401d1ac00f739b82e8cfd2046a4c392b5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularForm_HeckeOperator
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_FLTPrelim_Modularity
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularForm_isBoundedAtImInfty_heckeU

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ModularForm.isBoundedAtImInfty_heckeU {f : UpperHalfPlane → ℂ} (hf : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) (p : ℕ) : UpperHalfPlane.IsBoundedAtImInfty (ModularForm.heckeU k p f) := by
  revert f hf k p
  exact @_root_.P2MW.S_ModularForm_isBoundedAtImInfty_heckeU.solution
