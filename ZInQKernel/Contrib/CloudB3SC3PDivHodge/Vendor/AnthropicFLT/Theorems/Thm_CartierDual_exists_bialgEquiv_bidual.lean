/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CartierDual_exists_bialgEquiv_bidual
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_CartierDual
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_CartierDual_exists_bialgEquiv_bidual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem CartierDual.exists_bialgEquiv_bidual
    (R : Type*) [inst_t1 : CommRing R] (A : Type*) [inst_t2 : CommRing A] [inst_t3 : Bialgebra R A]
    [inst_t4 : Module.Finite R A] [inst_t5 : Module.Free R A] [inst_t6 : Coalgebra.IsCocomm R A] :
    ∃ e : A ≃ₐc[R] CartierDual R (CartierDual R A), ∀ (a : A) (φ : CartierDual R A), e a φ = φ a :=
  @_root_.P2MW.S_CartierDual_exists_bialgEquiv_bidual.solution R inst_t1 A inst_t2 inst_t3 inst_t4 inst_t5 inst_t6
