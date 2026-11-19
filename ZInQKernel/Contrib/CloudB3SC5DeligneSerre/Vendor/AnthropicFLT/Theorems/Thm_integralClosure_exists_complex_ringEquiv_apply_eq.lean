/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_integralClosure_exists_complex_ringEquiv_apply_eq (git blob 4338f938ec36cf6651f74708b927a8028f3154f2, sha256 cdddeeb568b296643b32d2312820ee058cbac9510ad6a6f1d328addbe647b01b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_integralClosure_exists_complex_ringEquiv_apply_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem integralClosure.exists_complex_ringEquiv_apply_eq (k : Type*) [Field k]
    (φ ψ : integralClosure ℤ ℂ →+* k) :
    ∃ σ : ℂ ≃+* ℂ, ∀ x y : integralClosure ℤ ℂ, (y : ℂ) = σ (x : ℂ) → φ x = ψ y := by
  revert k φ ψ
  exact @_root_.P2MW.S_integralClosure_exists_complex_ringEquiv_apply_eq.solution
