/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_IsLocalRing_exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.AdicCompletion.Noetherian
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_IsLocalRing_exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

universe u v
open IsLocalRing
theorem IsLocalRing.exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span
    {𝒪 : Type u} {R : Type v} [inst_t1 : CommRing 𝒪] [inst_t2 : IsLocalRing 𝒪] [inst_t3 : IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    [inst_t4 : CommRing R] [inst_t5 : Algebra 𝒪 R] [inst_t6 : IsLocalRing R] [inst_t7 : IsNoetherianRing R] [inst_t8 : IsAdicComplete (maximalIdeal R) R]
    (hres : Function.Surjective (⇑(residue R) ∘ ⇑(algebraMap 𝒪 R)))
    {r : ℕ} (a : Fin r → R) (ha : ∀ i, a i ∈ maximalIdeal R)
    (hgen : maximalIdeal R ≤
      Ideal.span (Set.range a) ⊔ maximalIdeal R ^ 2 ⊔ (maximalIdeal 𝒪).map (algebraMap 𝒪 R)) :
    ∃ ψ : MvPowerSeries (Fin r) 𝒪 →ₐ[𝒪] R, (∀ i, ψ (MvPowerSeries.X i) = a i) ∧ Function.Surjective ψ :=
  @_root_.P2MW.S_IsLocalRing_exists_mvPowerSeries_algHom_apply_X_eq_and_surjective_of_span.solution 𝒪 R inst_t1 inst_t2 inst_t3 inst_t4 inst_t5 inst_t6 inst_t7 inst_t8 hres r a ha hgen
