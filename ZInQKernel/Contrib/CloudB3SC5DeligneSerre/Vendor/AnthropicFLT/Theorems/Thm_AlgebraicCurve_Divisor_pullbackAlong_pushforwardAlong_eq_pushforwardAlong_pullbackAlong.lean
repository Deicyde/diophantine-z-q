/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong (git blob 23b8986e7c6e34803dcd8c372e05b733315bc4fa, sha256 142bd6d65e1f1cb048e84466ddac332743cd4b40fe434e56f47efa76a9043011).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import Mathlib.FieldTheory.Separable
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong {K F A B E : Type*} [Field K] [Field F] [Field A] [Field B] [Field E] [Algebra K F] [Algebra K A] [Algebra K B] [Algebra K E] [HasPrincipalDivisors K B] [HasPrincipalDivisors K E] (a : F →ₐ[K] A) (b : F →ₐ[K] B) (a' : A →ₐ[K] E) (b' : B →ₐ[K] E) (ha : a.toRingHom.IsIntegral) (hb : b.toRingHom.IsIntegral) (ha' : a'.toRingHom.IsIntegral) (hb' : b'.toRingHom.IsIntegral) (hsq : b'.comp b = a'.comp a) (hfin : FiniteAlong K (a'.comp a)) (hsep : SeparableAlong K (a'.comp a)) (hgen : Algebra.adjoin K (Set.range a' ∪ Set.range b') = ⊤) (hLD : finrankAlong K (a'.comp a) = finrankAlong K a * finrankAlong K b) (D : Divisor K A) : Divisor.pullbackAlong b hb (Divisor.pushforwardAlong a ha D) = Divisor.pushforwardAlong b' hb' (Divisor.pullbackAlong a' ha' D) := by
  revert K F A B E a b a' b' ha hb ha' hb' hsq hfin hsep hgen hLD D
  exact @_root_.P2MW.S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.solution
