/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem (git blob c6c12601036e32015013dcd0545f5733d185d3d3, sha256 6049b6b9378962ce525b762a2a097c8da5aee6c8abb1e31c3600d4ad281958ce).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Algebra.exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (f : F) [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (z : F) :
    ∃ q₀ : Algebra.adjoin L ({f} : Set F), q₀ ≠ 0 ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → (q₀ : F) * z ∈ V := by
  revert L F f z
  exact @_root_.P2MW.S_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem.solution
