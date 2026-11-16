/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem HopfAlgebra.exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType
    (K : Type*) [inst_t1 : Field K]
    (A : Type*) [inst_t2 : CommRing A] [inst_t3 : HopfAlgebra K A] [inst_t4 : Algebra.FiniteType K A] :
    ∃ (n : ℕ) (ξ : Fin n → A),
      (∀ i, ξ i ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ∧
      LinearIndependent K
        (fun i ↦ Ideal.Quotient.mk ((RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) (ξ i)) ∧
      (∀ a ∈ RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom,
        ∃ c : Fin n → K, a - ∑ i, c i • ξ i ∈ (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom) ^ 2) :=
  @_root_.P2MW.S_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType.solution K inst_t1 A inst_t2 inst_t3 inst_t4
