/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Algebra_Etale_eq_of_forall_algHom_apply_eq
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Pi
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_Algebra_Etale_eq_of_forall_algHom_apply_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem Algebra.Etale.eq_of_forall_algHom_apply_eq
    {K : Type*} [inst_t1 : Field K] {Ω : Type*} [inst_t2 : Field Ω] [inst_t3 : Algebra K Ω] [inst_t4 : IsAlgClosed Ω]
    {B : Type*} [inst_t5 : CommRing B] [inst_t6 : Algebra K B] [inst_t7 : Algebra.Etale K B]
    {x y : B} (h : ∀ χ : B →ₐ[K] Ω, χ x = χ y) : x = y :=
  @_root_.P2MW.S_Algebra_Etale_eq_of_forall_algHom_apply_eq.solution K inst_t1 Ω inst_t2 inst_t3 inst_t4 B inst_t5 inst_t6 inst_t7 x y h
