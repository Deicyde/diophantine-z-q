/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_CartierDual_forall_hopfKer_apply_eq_zero_iff_mem_map_ker_counit
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_HopfKer
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_CartierDual
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_CartierDualInstances
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_CartierDualMap
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_CartierDual_forall_hopfKer_apply_eq_zero_iff_mem_map_ker_counit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

universe u v w

theorem CartierDual.forall_hopfKer_apply_eq_zero_iff_mem_map_ker_counit
    {R : Type u} [inst_t1 : CommRing R]
    {A : Type v} [inst_t2 : CommRing A] [inst_t3 : HopfAlgebra R A] [inst_t4 : Module.Finite R A] [inst_t5 : Module.Free R A]
    [inst_t6 : Coalgebra.IsCocomm R A]
    {B : Type w} [inst_t7 : CommRing B] [inst_t8 : HopfAlgebra R B] [inst_t9 : Module.Finite R B] [inst_t10 : Module.Free R B]
    [inst_t11 : Coalgebra.IsCocomm R B]
    (π : A →ₐc[R] B) (hπ : Function.Surjective π) (φ : CartierDual R A) :
    (∀ a ∈ HopfAlgebra.hopfKer π, φ a = 0) ↔
      φ ∈ Ideal.map (CartierDual.map π)
        (RingHom.ker (Bialgebra.counitAlgHom R (CartierDual R B))) :=
  @_root_.P2MW.S_CartierDual_forall_hopfKer_apply_eq_zero_iff_mem_map_ker_counit.solution R inst_t1 A inst_t2 inst_t3 inst_t4 inst_t5 inst_t6 B inst_t7 inst_t8 inst_t9 inst_t10 inst_t11 π hπ φ
