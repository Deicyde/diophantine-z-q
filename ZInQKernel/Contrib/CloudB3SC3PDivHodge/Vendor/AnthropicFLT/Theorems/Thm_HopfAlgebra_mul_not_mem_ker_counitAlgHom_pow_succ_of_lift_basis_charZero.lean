/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem HopfAlgebra.mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero
    (K : Type*) [inst_t1 : Field K] [inst_t2 : CharZero K]
    (A : Type*) [inst_t3 : CommRing A] [inst_t4 : HopfAlgebra K A]
    {ι : Type*} [inst_t5 : Fintype ι] {ξ : ι → A}
    (hξI : ∀ i, ξ i ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom)
    (hξli : LinearIndependent K
      (fun i ↦ Ideal.Quotient.mk ((RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) (ξ i)))
    (hξspan : ∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom,
      ∃ c : ι → K, a - ∑ i, c i • ξ i ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2)
    {m n : ℕ} {x y : A}
    (hxm : x ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ m)
    (hxm' : x ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (m + 1))
    (hyn : y ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ n)
    (hyn' : y ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (n + 1)) :
    x * y ∉ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ (m + n + 1) :=
  @_root_.P2MW.S_HopfAlgebra_mul_not_mem_ker_counitAlgHom_pow_succ_of_lift_basis_charZero.solution K inst_t1 inst_t2 A inst_t3 inst_t4 ι inst_t5 ξ hξI hξli hξspan m n x y hxm hxm' hyn hyn'
