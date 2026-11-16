/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Algebra.Etale.natCard_algHom_eq_finrank_of_isAlgClosed
    (k : Type*) [inst_t1 : Field k] [inst_t2 : IsAlgClosed k] (R : Type*) [inst_t3 : CommRing R] [inst_t4 : Algebra k R] [inst_t5 : Algebra.Etale k R] :
    Nat.card (R →ₐ[k] k) = Module.finrank k R :=
  @_root_.P2MW.S_Algebra_Etale_natCard_algHom_eq_finrank_of_isAlgClosed.solution k inst_t1 inst_t2 R inst_t3 inst_t4 inst_t5
