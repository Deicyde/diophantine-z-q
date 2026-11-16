/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HopfAlgebra_finite_projective_hopfKer_of_surjective
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_HopfKer
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_HopfAlgebra_finite_projective_hopfKer_of_surjective

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u v w
theorem HopfAlgebra.finite_projective_hopfKer_of_surjective {R : Type u} [inst_t1 : CommRing R] {A : Type v} [inst_t2 : CommRing A] [inst_t3 : HopfAlgebra R A]
    {B : Type w} [inst_t4 : CommRing B] [inst_t5 : HopfAlgebra R B] [inst_t6 : Module.Finite R B] [inst_t7 : Module.Free R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) :
    Module.Finite ↥(HopfAlgebra.hopfKer π) A ∧ Module.Projective ↥(HopfAlgebra.hopfKer π) A :=
  @_root_.P2MW.S_HopfAlgebra_finite_projective_hopfKer_of_surjective.solution R inst_t1 A inst_t2 inst_t3 B inst_t4 inst_t5 inst_t6 inst_t7 π hπ
