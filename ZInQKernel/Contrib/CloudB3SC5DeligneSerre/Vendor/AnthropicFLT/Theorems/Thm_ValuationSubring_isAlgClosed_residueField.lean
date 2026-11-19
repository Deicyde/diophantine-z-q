/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ValuationSubring_isAlgClosed_residueField (git blob 2a212ad7773818e5deb515885bf205cf38f89bfc, sha256 82d1e74a0ae7a5d4633e0432595eac044a9c71a635afa7d6924b7e47aca25f6f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ValuationSubring_isAlgClosed_residueField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem ValuationSubring.isAlgClosed_residueField {K : Type*} [Field K] [IsAlgClosed K]
    (A : ValuationSubring K) : IsAlgClosed (IsLocalRing.ResidueField A) := by
  revert K A
  exact @_root_.P2MW.S_ValuationSubring_isAlgClosed_residueField.solution
