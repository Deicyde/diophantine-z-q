/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u v

theorem HopfAlgebra.finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero
    (k : Type u) [inst_t1 : Field k] (p : ℕ) [inst_t2 : Fact p.Prime] [inst_t3 : CharP k p]
    (A : Type v) [inst_t4 : CommRing A] [inst_t5 : Bialgebra k A] [inst_t6 : Module.Finite k A]
    (hA : ∀ a : A, Coalgebra.counit (R := k) a = 0 → a ^ p = 0) :
    Module.finrank k A =
      p ^ Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent :=
  @_root_.P2MW.S_HopfAlgebra_finrank_eq_pow_finrank_cotangent_of_forall_pow_prime_eq_zero.solution k inst_t1 p inst_t2 inst_t3 A inst_t4 inst_t5 inst_t6 hA
