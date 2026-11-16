/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.FieldTheory.IsAlgClosed.Basic
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem HopfAlgebra.isReduced_of_finiteType_of_isAlgClosed_of_charZero
    (K : Type*) [inst_t1 : Field K] [inst_t2 : CharZero K] [inst_t3 : IsAlgClosed K]
    (A : Type*) [inst_t4 : CommRing A] [inst_t5 : HopfAlgebra K A] [inst_t6 : Algebra.FiniteType K A] :
    IsReduced A :=
  @_root_.P2MW.S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero.solution K inst_t1 inst_t2 inst_t3 A inst_t4 inst_t5 inst_t6
