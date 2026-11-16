/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_isOpen_setOf_restrictScalars_smul_points_eq
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_Points
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_isOpen_setOf_restrictScalars_smul_points_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PDivisibleGroup.isOpen_setOf_restrictScalars_smul_points_eq
    {R : Type} [inst_t1 : CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (K L : Type) [inst_t2 : Field K] [inst_t3 : Field L] [inst_t4 : Algebra R K] [inst_t5 : Algebra R L] [inst_t6 : Algebra K L]
    [inst_t7 : IsScalarTower R K L] [inst_t8 : Algebra.IsAlgebraic K L] (z : G.Points L) :
    IsOpen {σ : L ≃ₐ[K] L | σ.restrictScalars R • z = z} :=
  @_root_.P2MW.S_PDivisibleGroup_isOpen_setOf_restrictScalars_smul_points_eq.solution R inst_t1 p h G K L inst_t2 inst_t3 inst_t4 inst_t5 inst_t6 inst_t7 inst_t8 z
