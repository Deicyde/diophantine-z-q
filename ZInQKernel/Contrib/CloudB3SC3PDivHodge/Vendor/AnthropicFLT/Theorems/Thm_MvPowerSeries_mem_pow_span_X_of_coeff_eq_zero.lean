/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u v w
theorem MvPowerSeries.mem_pow_span_X_of_coeff_eq_zero {σ : Type u} {R : Type v} [inst_t1 : Finite σ] [inst_t2 : CommRing R] (k : ℕ) (φ : MvPowerSeries σ R) (hφ : ∀ m : σ →₀ ℕ, m.degree < k → MvPowerSeries.coeff m φ = 0) : φ ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) ^ k :=
  @_root_.P2MW.S_MvPowerSeries_mem_pow_span_X_of_coeff_eq_zero.solution σ R inst_t1 inst_t2 k φ hφ
