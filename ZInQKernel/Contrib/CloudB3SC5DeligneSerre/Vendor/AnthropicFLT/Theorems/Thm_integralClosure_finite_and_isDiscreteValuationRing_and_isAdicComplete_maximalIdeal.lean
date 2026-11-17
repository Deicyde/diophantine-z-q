/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal (git blob b9f656c48a2ed0ad038f3f9ab4922ea321910efc, sha256 04dfacebd816e8dd09836abb1f869278ad39fb1ff1dcf631837a6ab3c1fbf255).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
    (𝒪 : Type*) [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪]
    [IsAdicComplete (IsLocalRing.maximalIdeal 𝒪) 𝒪]
    (L : Type*) [Field L] [Algebra 𝒪 L] [IsFractionRing 𝒪 L]
    (L' : Type*) [Field L'] [Algebra 𝒪 L'] [Algebra L L'] [IsScalarTower 𝒪 L L']
    [FiniteDimensional L L'] [Algebra.IsSeparable L L'] :
    Module.Finite 𝒪 (integralClosure 𝒪 L') ∧
    ∃ _ : IsDiscreteValuationRing (integralClosure 𝒪 L'),
      IsAdicComplete (IsLocalRing.maximalIdeal (integralClosure 𝒪 L'))
        (integralClosure 𝒪 L') := by
  revert 𝒪 L L'
  exact @_root_.P2MW.S_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal.solution
