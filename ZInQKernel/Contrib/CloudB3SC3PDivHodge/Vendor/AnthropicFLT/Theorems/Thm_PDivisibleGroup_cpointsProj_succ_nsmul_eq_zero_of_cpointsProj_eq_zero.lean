/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_CompletedPoints
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PDivisibleGroup.cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero
    {R : Type} [inst_t1 : CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (S : Type) [inst_t2 : CommRing S] [inst_t3 : Algebra R S] (g : G.CPoints S) {i : ℕ} (hi : 1 ≤ i)
    (hg : G.cpointsProj S i g = 0) :
    G.cpointsProj S (i + 1) (p • g) = 0 :=
  @_root_.P2MW.S_PDivisibleGroup_cpointsProj_succ_nsmul_eq_zero_of_cpointsProj_eq_zero.solution R inst_t1 p h G S inst_t2 inst_t3 g i hi hg
