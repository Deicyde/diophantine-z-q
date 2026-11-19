/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Divisor_pushforward_div (git blob 52bc3aeca6e7cca89d78ce670e8585c27f6da084, sha256 d297917e512c76ca683915ee1645e248cef463c03d3504bab6561a7542726e2f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorPushPull
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Divisor_pushforwardNormFormula

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Divisor_pushforward_div

open AlgebraicCurve AlgebraicCurve.Divisor

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F] [HasPrincipalDivisors K F'] {f : F'} (hf : f ≠ 0) {D : Divisor K F'} (hD : ∀ w, D w = w.ord f) {E : Divisor K F} (hE : ∀ v, E v = v.ord (Algebra.norm F f)) : Divisor.pushforward F D = E :=
  pushforward_eq_of_normFormula AlgebraicCurve.Divisor.pushforwardNormFormula hf hD hE
