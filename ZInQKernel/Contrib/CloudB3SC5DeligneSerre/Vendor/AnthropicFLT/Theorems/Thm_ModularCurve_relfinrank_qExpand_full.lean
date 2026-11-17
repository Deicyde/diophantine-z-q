/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_relfinrank_qExpand_full (git blob e5820646611ff8a13abd3ddacf66a98f472aa448, sha256 d76e305b9377b2fd4db262b2f9b98f38464248091e73daa6e219025c8b5425df).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import Mathlib.FieldTheory.Relrank
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_relfinrank_qExpand_full

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve
theorem ModularCurve.relfinrank_qExpand_full (N ℓ : ℕ) [NeZero N] [hl : Fact (Nat.Prime ℓ)] : IntermediateField.relfinrank ((modularFunctionFieldFull N).map (qExpandₐ ℓ)) (modularFunctionFieldFull (N * ℓ)) = if ℓ ∣ N then ℓ else ℓ + 1 := by
  revert N ℓ hl
  exact @_root_.P2MW.S_ModularCurve_relfinrank_qExpand_full.solution
