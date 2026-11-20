/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime (git blob 86426f4c295d4af76a4ea2655a2e70ea379a6d4a, sha256 b73163d8f28ec1cd72f4ee7b39c659c56a1462a3042e628cb99a32e78bd1180f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_AtkinLehner
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_isFrickeAutFull

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_isFrickeAutFull_frickeInvolutionFull_prime

set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField

noncomputable section

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : IsFrickeAutFull ℓ (frickeInvolutionFull ℓ) := by
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  exact ModularCurve.isFrickeAutFull_frickeInvolutionFull ℓ (ModularCurve.exists_isFrickeAutFull ℓ)

end
