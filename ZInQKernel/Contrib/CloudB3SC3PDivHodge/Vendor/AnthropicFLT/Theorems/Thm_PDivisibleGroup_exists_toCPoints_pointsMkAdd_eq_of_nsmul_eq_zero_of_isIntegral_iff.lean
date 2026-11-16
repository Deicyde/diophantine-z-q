/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_CompletedPoints
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PDivisibleGroup.exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff
    (p : ℕ) [inst_t1 : Fact p.Prime] {R : Type} [inst_t2 : CommRing R] [inst_t3 : Algebra R (PadicAlgCl p)]
    (hO : ∀ x : PadicAlgCl p, IsIntegral R x ↔ ‖x‖ ≤ 1)
    {h : ℕ} (G : PDivisibleGroup R p h) (k : ℕ)
    (T : G.CPoints (integralClosure R (PadicAlgCl p))) (hT : (p ^ k) • T = 0) :
    ∃ t : G.Point (integralClosure R (PadicAlgCl p)) k,
      G.toCPoints (integralClosure R (PadicAlgCl p))
        (G.pointsMkAdd (integralClosure R (PadicAlgCl p)) k (Additive.ofMul t)) = T :=
  @_root_.P2MW.S_PDivisibleGroup_exists_toCPoints_pointsMkAdd_eq_of_nsmul_eq_zero_of_isIntegral_iff.solution p inst_t1 R inst_t2 inst_t3 hO h G k T hT
