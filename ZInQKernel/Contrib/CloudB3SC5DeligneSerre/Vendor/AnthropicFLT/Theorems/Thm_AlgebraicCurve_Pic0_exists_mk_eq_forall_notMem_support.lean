/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support (git blob bcaab8d0866d8ebfb1f91279b059985ded654f33, sha256 af04d5302e4a0d309129e91865c4894f2ed552cf1cc68b5b8880498cd366ad09).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Pic0.exists_mk_eq_forall_notMem_support {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F] (x : Pic0 K F) (S : Finset (Place K F)) :
    ∃ D : Divisor.degZero (K := K) (F := F), Pic0.mk D = x ∧ ∀ v ∈ (D : Divisor K F).support, v ∉ S := by
  revert K F x S
  exact @_root_.P2MW.S_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support.solution
