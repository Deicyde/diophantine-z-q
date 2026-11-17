/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable (git blob 608596719af2b0d6ee2084f99aef5e35dd97a710, sha256 99af2be0028a52d856fddc011f70f72b92617a303586e3acd715e382cabf01f7).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import Mathlib.FieldTheory.RatFunc.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicCurve
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
theorem AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable
    {K : Type*} [Field K] (E : Type*) [Field E] [Algebra K E]
    [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E] [Algebra.IsSeparable (RatFunc K) E] :
    HasPrincipalDivisors K E := by
  revert K E
  exact @_root_.P2MW.S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_of_isSeparable.solution
