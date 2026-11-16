/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_cotangentBaseChange_bijective
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_BaseChange
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_cotangentBaseChange_bijective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PDivisibleGroup.cotangentBaseChange_bijective
    {R : Type} [inst_t1 : CommRing R] {p h : ℕ} (G : PDivisibleGroup R p h)
    (S : Type) [inst_t2 : CommRing S] [inst_t3 : Algebra R S] [inst_t4 : Nontrivial S] (v : ℕ) :
    Function.Bijective (G.cotangentBaseChange S v) :=
  @_root_.P2MW.S_PDivisibleGroup_cotangentBaseChange_bijective.solution R inst_t1 p h G S inst_t2 inst_t3 inst_t4 v
