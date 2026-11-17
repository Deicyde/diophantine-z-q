/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_NeronModelInfra_TopFormOrder_addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.P2M.Sol.S_NeronModelInfra_TopFormOrder_addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

universe u

open NeronModelInfra.TopFormOrder

theorem NeronModelInfra.TopFormOrder.addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer
    (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (L : Type u) [Field L] [Algebra O L] [IsFractionRing O L] :
    (∀ a b : L, a ≠ 0 → b ≠ 0 → addOrd O L (a * b) = addOrd O L a + addOrd O L b) ∧
    (∀ x : O, 0 ≤ addOrd O L (algebraMap O L x)) ∧
    (∀ x : O, x ≠ 0 → (addOrd O L (algebraMap O L x) = 0 ↔ IsUnit x)) ∧
    (∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R' O]
      [IsLocalHom (algebraMap R' O)],
      Ideal.map (algebraMap R' O) (IsLocalRing.maximalIdeal R') = IsLocalRing.maximalIdeal O →
      ∀ π : R', IsLocalRing.maximalIdeal R' = Ideal.span {π} →
        addOrd O L (algebraMap O L (algebraMap R' O π)) = 1) := by p2m_exact_reverting @_root_.P2MW.S_NeronModelInfra_TopFormOrder_addOrd_mul_and_nonneg_and_eq_zero_iff_and_uniformizer.solution
