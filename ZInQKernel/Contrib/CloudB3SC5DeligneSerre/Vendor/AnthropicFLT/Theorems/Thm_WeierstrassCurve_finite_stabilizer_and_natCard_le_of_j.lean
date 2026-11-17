/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j (git blob ef912d9d01e34290b39673be875a7ee95073ce18, sha256 ac5b7b639da1b39a14edc6c24d5fa7fd80f3c2e20c2ce012776fca6c92dd47a8).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open WeierstrassCurve

theorem WeierstrassCurve.finite_stabilizer_and_natCard_le_of_j
    {F : Type*} [Field F] (E : WeierstrassCurve F) [E.IsElliptic] :
    ((6 : F) ≠ 0 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 6) ∧
    ((6 : F) ≠ 0 → E.j = 1728 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 4) ∧
    (ringChar F = 3 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 12) ∧
    (ringChar F = 2 → E.j = 0 →
      Finite (MulAction.stabilizer (VariableChange F) E) ∧
        Nat.card (MulAction.stabilizer (VariableChange F) E) ≤ 24) := by
  revert F E
  exact @_root_.P2MW.S_WeierstrassCurve_finite_stabilizer_and_natCard_le_of_j.solution
