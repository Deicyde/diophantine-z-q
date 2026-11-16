/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
Modified for the Z-in-Q kernel (2026-11-16, p-divisible Hodge-Tate port): local import paths
are relocated, the P2M.Util elaborators are replaced by standard Lean commands or explicit terms,
local notations are expanded in place, and the upstream lakefile options are set as `set_option`
lines after the imports; see ZInQKernel/Contrib/CloudB3SC3PDivHodge/PORTING.md. Any other change is marked `-- [port]`.
Original copyright/attribution notices: NOTICE.upstream and ATTRIBUTION.upstream.md in
ZInQKernel/Contrib/CloudB3SC3PDivHodge/Vendor/AnthropicFLT/; license: LICENSE in that directory.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC3PDivHodge.Vendor.AnthropicFLT.P2M.Sol.S_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
    (𝒪 : Type*) [inst_t1 : CommRing 𝒪] [inst_t2 : IsDomain 𝒪] [inst_t3 : IsDiscreteValuationRing 𝒪]
    [inst_t4 : IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (L : Type*) [inst_t5 : Field L] [inst_t6 : Algebra 𝒪 L] [inst_t7 : IsFractionRing 𝒪 L]
    (L' : Type*) [inst_t8 : Field L'] [inst_t9 : Algebra 𝒪 L'] [inst_t10 : Algebra L L'] [inst_t11 : IsScalarTower 𝒪 L L']
    [inst_t12 : FiniteDimensional L L'] [inst_t13 : Algebra.IsSeparable L L'] :
    Module.Finite 𝒪 (integralClosure 𝒪 L') ∧
    ∃ _ : IsDiscreteValuationRing (integralClosure 𝒪 L'),
      IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure 𝒪 L'))
        (integralClosure 𝒪 L') :=
  @_root_.P2MW.S_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal.solution 𝒪 inst_t1 inst_t2 inst_t3 inst_t4 L inst_t5 inst_t6 inst_t7 L' inst_t8 inst_t9 inst_t10 inst_t11 inst_t12 inst_t13
