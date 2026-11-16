/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_MvPowerSeries_exists_algHom_apply_X_eq
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_MvPowerSeries_exists_algHom_apply_X_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u v w
theorem MvPowerSeries.exists_algHom_apply_X_eq {σ : Type u} {𝒪 : Type v} {A : Type w} [inst_t1 : Finite σ] [inst_t2 : CommRing 𝒪] [inst_t3 : CommRing A] [inst_t4 : Algebra 𝒪 A] (I : Ideal A) [inst_t5 : IsAdicComplete I A] (a : σ → A) (ha : ∀ i, a i ∈ I) : ∃ φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A, ∀ i, φ (MvPowerSeries.X i) = a i :=
  @_root_.P2MW.S_MvPowerSeries_exists_algHom_apply_X_eq.solution σ 𝒪 A inst_t1 inst_t2 inst_t3 inst_t4 I inst_t5 a ha
