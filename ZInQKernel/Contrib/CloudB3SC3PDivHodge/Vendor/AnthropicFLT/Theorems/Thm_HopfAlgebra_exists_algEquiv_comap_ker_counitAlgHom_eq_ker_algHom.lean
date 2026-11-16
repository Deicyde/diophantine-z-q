/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem HopfAlgebra.exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom
    (K : Type*) [inst_t1 : Field K]
    (A : Type*) [inst_t2 : CommRing A] [inst_t3 : HopfAlgebra K A] (χ : A →ₐ[K] K) :
    ∃ e : A ≃ₐ[K] A,
      (RingHom.ker (Bialgebra.counitAlgHom K A).toRingHom).comap e.toRingEquiv.toRingHom
        = RingHom.ker χ.toRingHom :=
  @_root_.P2MW.S_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom.solution K inst_t1 A inst_t2 inst_t3 χ
