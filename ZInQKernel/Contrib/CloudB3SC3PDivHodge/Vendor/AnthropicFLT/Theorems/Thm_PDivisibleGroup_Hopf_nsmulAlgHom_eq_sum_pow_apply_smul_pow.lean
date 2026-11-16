/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PDivisibleGroup_Hopf_nsmulAlgHom_eq_sum_pow_apply_smul_pow
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_HopfAlgebra_CartierDual
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.Definitions.Def_PDivisibleGroup_Basic
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PDivisibleGroup_Hopf_nsmulAlgHom_eq_sum_pow_apply_smul_pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u v w

theorem PDivisibleGroup.Hopf.nsmulAlgHom_eq_sum_pow_apply_smul_pow
    {R : Type u} [inst_t1 : CommRing R] {p : ℕ} [inst_t2 : Fact p.Prime] [inst_t3 : CharP R p]
    {A : Type v} [inst_t4 : CommRing A] [inst_t5 : Bialgebra R A] [inst_t6 : Coalgebra.IsCocomm R A]
    {ι : Type w} [inst_t7 : Fintype ι] (b : Module.Basis ι R A) (a : A) :
    PDivisibleGroup.Hopf.nsmulAlgHom R A p a =
      ∑ i, (CartierDual.ofDual R A (b.coord i) ^ p) a • b i ^ p :=
  @_root_.P2MW.S_PDivisibleGroup_Hopf_nsmulAlgHom_eq_sum_pow_apply_smul_pow.solution R inst_t1 p inst_t2 inst_t3 A inst_t4 inst_t5 inst_t6 ι inst_t7 b a
