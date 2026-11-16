/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Apache License 2.0; see LICENSE, NOTICE.upstream and ATTRIBUTION.upstream.md.
W28 compatibility changes: relocated imports; removed imported-only global attribute
suppressions and unused P2M.Util; direct exact solution wrappers; upstream Lake options
made explicit below. Exact bridge cuts, when present, are recorded in SOURCE_MANIFEST.json.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.Definitions.Def_QuaternionAlgebra_EichlerOrder
import ZInQKernel.Contrib.CloudB4W28FineModuli.Vendor.AnthropicFLT.P2M.Sol.S_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem QuaternionAlgebra.forall_isUnit_iff_forall_normForm_eq_zero
    (K : Type) [Field K] (a b : K) :
    (∀ x : ℍ[K, a, b], x ≠ 0 → IsUnit x) ↔
      ∀ x₀ x₁ x₂ x₃ : K, x₀ ^ 2 - a * x₁ ^ 2 - b * x₂ ^ 2 + a * b * x₃ ^ 2 = 0 →
        x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0 := by apply @_root_.P2MW.S_QuaternionAlgebra_forall_isUnit_iff_forall_normForm_eq_zero.solution <;> assumption
