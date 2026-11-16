/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_PadicAlgCl_norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_PadicAlgCl_norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

theorem PadicAlgCl.norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one
    (p : ℕ) [inst_t1 : Fact p.Prime] (F : IntermediateField ℚ_[p] (PadicAlgCl p)) [inst_t2 : FiniteDimensional ℚ_[p] F]
    (E : IntermediateField F (PadicAlgCl p)) [inst_t3 : FiniteDimensional F E] {α : E}
    (hα : ‖(α : PadicAlgCl p)‖ ≤ 1) (hgen : IntermediateField.adjoin F {α} = ⊤) (z : E)
    (hz : ∀ w : E, ‖(w : PadicAlgCl p)‖ ≤ 1 →
      ‖((Algebra.trace F E (z * w) : F) : PadicAlgCl p)‖ ≤ 1) :
    ‖((z * Polynomial.aeval α (Polynomial.derivative (minpoly F α)) : E) : PadicAlgCl p)‖ ≤ 1 :=
  @_root_.P2MW.S_PadicAlgCl_norm_mul_aeval_derivative_minpoly_le_one_of_forall_norm_trace_mul_le_one.solution p inst_t1 F inst_t2 E inst_t3 α hα hgen z hz
