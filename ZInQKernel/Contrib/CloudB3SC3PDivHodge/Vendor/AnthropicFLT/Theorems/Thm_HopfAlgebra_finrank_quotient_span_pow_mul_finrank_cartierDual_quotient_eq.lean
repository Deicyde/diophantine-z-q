/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HopfAlgebra_finrank_quotient_span_pow_mul_finrank_cartierDual_quotient_eq
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_CartierDual
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_HopfAlgebra_finrank_quotient_span_pow_mul_finrank_cartierDual_quotient_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

attribute [-instance] CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra
attribute [-simp] CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul

set_option autoImplicit false

universe u v

theorem HopfAlgebra.finrank_quotient_span_pow_mul_finrank_cartierDual_quotient_eq
    (k : Type u) [inst_t1 : Field k] (p : ℕ) [inst_t2 : Fact p.Prime] [inst_t3 : CharP k p]
    (H : Type v) [inst_t4 : CommRing H] [inst_t5 : HopfAlgebra k H] [inst_t6 : Module.Finite k H] [inst_t7 : Coalgebra.IsCocomm k H] :
    Module.finrank k (H ⧸ Ideal.span ((fun a : H => a ^ p) ''
        (RingHom.ker (Bialgebra.counitAlgHom k H) : Set H))) *
      Module.finrank k (CartierDual k H ⧸ Ideal.span {φ : CartierDual k H | φ 1 = 0 ∧
        ∀ x ∈ Ideal.span ((fun a : H => a ^ p) '' (RingHom.ker (Bialgebra.counitAlgHom k H) : Set H)),
          φ x = 0}) =
      Module.finrank k H :=
  @_root_.P2MW.S_HopfAlgebra_finrank_quotient_span_pow_mul_finrank_cartierDual_quotient_eq.solution k inst_t1 p inst_t2 inst_t3 H inst_t4 inst_t5 inst_t6 inst_t7
