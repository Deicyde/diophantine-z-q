/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible (git blob ea47bf28d15c1713bd21208f79b76e502ae95581, sha256 f7af703503dd4f3756d98372ea03ef59b215ec29a214c796bfbbdcc91c9d27b5).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible.{u, v} {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [HasPrincipalDivisors K F] {n : ℕ} [NeZero n]
    (hdiv : ∀ (L' : Type v) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
      [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L'],
      ∀ (n : ℤ), n ≠ 0 → ∀ x : Pic0 K L', ∃ y, n • y = x)
    (e : DivisorialWeilPairingData K F n) : Function.Injective e.toHom := by
  revert K F n hdiv e
  exact @_root_.P2MW.S_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible.solution
