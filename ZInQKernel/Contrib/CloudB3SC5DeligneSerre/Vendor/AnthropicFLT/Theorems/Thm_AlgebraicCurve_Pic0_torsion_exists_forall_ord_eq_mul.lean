/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul (git blob efa333c4c61e6c81426f09522928abedc06e4283, sha256 a033baa499d2950a93934a512630fae167956c9618e3434d52034c6a894d0758).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
theorem AlgebraicCurve.Pic0.torsion.exists_forall_ord_eq_mul {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (x : Pic0.torsion K F n) (D : Divisor.degZero (K := K) (F := F)) (hD : Pic0.mk D = (x : Pic0 K F)) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v := by
  revert K F n x D hD
  exact @_root_.P2MW.S_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul.solution
