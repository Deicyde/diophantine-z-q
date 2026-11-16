/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u v w
theorem HopfAlgebra.natCard_algHom_eq_finrank_of_charZero (R : Type u) [inst_t1 : CommRing R] (H : Type v) [inst_t2 : CommRing H] [inst_t3 : HopfAlgebra R H]
    [inst_t4 : Module.Finite R H] [inst_t5 : Module.Free R H]
    (K : Type w) [inst_t6 : Field K] [inst_t7 : IsAlgClosed K] [inst_t8 : CharZero K] [inst_t9 : Algebra R K] :
    Nat.card (H →ₐ[R] K) = Module.finrank R H :=
  @_root_.P2MW.S_HopfAlgebra_natCard_algHom_eq_finrank_of_charZero.solution R inst_t1 H inst_t2 inst_t3 inst_t4 inst_t5 K inst_t6 inst_t7 inst_t8 inst_t9
