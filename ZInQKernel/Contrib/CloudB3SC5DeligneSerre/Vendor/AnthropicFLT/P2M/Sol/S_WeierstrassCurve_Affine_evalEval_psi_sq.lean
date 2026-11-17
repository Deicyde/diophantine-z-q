/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_WeierstrassCurve_Affine_evalEval_psi_sq (git blob 88a712dd26a79e8dcb9a9bab89de21c768a89c91, sha256 d23f16526bb30088864b65bc7f12b09a8660a34cfcc63141e38c1798d7b17686).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_WeierstrassCurve_Affine_evalEval_psi_sq

open Polynomial
open scoped Polynomial.Bivariate

theorem PortCard.evalEval_ψ_sq {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x := by
  have hmk : WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ n ^ 2) =
      WeierstrassCurve.Affine.CoordinateRing.mk W (C (W.ΨSq n)) := by
    rw [map_pow, WeierstrassCurve.Affine.CoordinateRing.mk_ψ,
      WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq]
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp hmk
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_pow, evalEval_C] at h1
  exact h1

theorem PortCard.evalEval_φ {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) (n : ℤ) : (W.φ n).evalEval x y = (W.Φ n).eval x := by
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_eq_mk.mp (WeierstrassCurve.Affine.CoordinateRing.mk_φ W n)
  have h0 : (W.toAffine.polynomial).evalEval x y = 0 := h
  have h1 := congrArg (evalEval x y) hp
  rw [evalEval_sub, evalEval_mul, h0, zero_mul, sub_eq_zero, evalEval_C] at h1
  exact h1

theorem solution {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R} (h : W.toAffine.Equation x y) (n : ℤ) : (W.ψ n).evalEval x y ^ 2 = (W.ΨSq n).eval x :=
  PortCard.evalEval_ψ_sq W h n
