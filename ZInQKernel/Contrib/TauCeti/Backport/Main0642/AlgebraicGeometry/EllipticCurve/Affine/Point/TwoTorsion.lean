/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 0642eae29e0a, module
-- TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which
-- is vendored as `ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion` (task selmer-2infty).
-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten.
module

public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion
public import Mathlib.Algebra.Module.Torsion.Basic
public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.TwoTorsion
public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Basic

/-!
# Translation by a point of order two, and the `x`-coordinate of a double

Let `W` be a Weierstrass curve over a field `F`, and let `T = (e, t)` be an affine point of order
two, so that `ψ₂(e, t) = 2t + a₁e + a₃` vanishes, and write `c_T = -W_X(e, t)` as in
`TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.TwoTorsion`.

An affine point `(x, y)` has order two exactly when `ψ₂(x, y) = 0`, and the points `S` with
`2S = O` (the `2`-torsion) are `O`, `T` and the points `(e₀, t₀)` with `ψ₂(e₀, t₀) = 0` and
`e₀ ≠ e`. This file records these facts and the formulas in which `c_T` appears, valid in every
characteristic.

* Translation by `T` inverts `x - e` up to `c_T`: for an affine point `P = (x, y)` with `x ≠ e`,
  `(x(P + T) - e)(x - e) = c_T`, and `ψ₂(P + T)(x - e) = -ψ₂(P)(x(P + T) - e)`.
* The `x`-coordinate of a double is `e` plus a square: for `P = (x, y)` with `ψ₂(x, y) ≠ 0`,
  `(x(2P) - e) ψ₂(x, y)² = ((x - e)² - c_T)²`.

The second formula says that `x - e`, as a function on the curve, becomes a square after pulling
back along multiplication by `2`, with square root `((x - e)² - c_T) / ψ₂`; the first says how that
root transforms under translation by the points of order two. Together they compute the Kummer map
of multiplication by `2` (Silverman X.1.4).

## Main results

* `WeierstrassCurve.Affine.Point.some_add_self_eq_zero_iff`: `(x, y)` has order two exactly when
  `ψ₂(x, y) = 0`.
* `WeierstrassCurve.Affine.Point.some_mem_torsionBy_two`: such a point lies in `E[2]`.
* `WeierstrassCurve.Affine.Point.eq_zero_or_eq_or_exists_of_add_self_eq_zero`: a point `S` with
  `2S = O` is `O`, `T`, or a point of order two over another root.
* `WeierstrassCurve.Affine.Point.xCoord_add_sub_mul_sub`: `(x(P + T) - e)(x - e) = c_T`.
* `WeierstrassCurve.Affine.Point.evalEval_polynomialY_add_mul_sub`:
  `ψ₂(P + T)(x - e) = -ψ₂(P)(x(P + T) - e)`.
* `WeierstrassCurve.Affine.Point.xCoord_add_self_sub_mul_sq`:
  `(x(2P) - e) ψ₂(P)² = ((x - e)² - c_T)²`.
* `WeierstrassCurve.Affine.Point.sq_xCoord_add_sub_add_evalEval_polynomialX_div`: the square root
  `((x - e)² - c_T) / ψ₂` of `x(2P) - e` is fixed by translation by `O` and `T`, and changes sign
  under translation by the other two points of order two.
* `WeierstrassCurve.Affine.Point.two_ne_zero_of_two_lt_card`: more than two points of order
  dividing two force `2 ≠ 0` (for an elliptic curve).
* `WeierstrassCurve.Affine.Point.xCoord_add_sub`: when `(x - e)² = c_T`, translation by a point
  of order two sends `x - e` to `±(x - e)`, with the same signs.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.3 and X.1.4.
-/

public section

namespace WeierstrassCurve.Affine

open Point

variable {F : Type*} [Field F] [DecidableEq F] {W : Affine F} {e t x y : F}

/-- An affine point at which `ψ₂` vanishes is killed by two. -/
theorem Point.some_mem_torsionBy_two (h : W.Nonsingular x y)
    (hy : W.polynomialY.evalEval x y = 0) : some x y h ∈ AddSubgroup.torsionBy W.Point (2 : ℕ) := by
  rw [AddSubgroup.torsionBy.nsmul_iff, two_nsmul, (some_add_self_eq_zero_iff h).2 hy]

omit [DecidableEq F] in
/-- More than two points of order dividing two force `2 ≠ 0`: in characteristic two the affine
points of order dividing two lie on `a₁x + a₃ = 0`, and there is at most one of them. -/
theorem Point.two_ne_zero_of_two_lt_card [W.IsElliptic] {S : Finset W.Point}
    (hS : ∀ T ∈ S, -T = T) (hcard : 2 < S.card) : (2 : F) ≠ 0 := by
  classical
  intro h2
  let _ : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2
  -- An affine point of order dividing two satisfies `a₁x + a₃ = 0`, as `2y + a₁x + a₃ = 0`.
  have hlin {x y : F} (h : W.Nonsingular x y) (hT : -Point.some x y h = Point.some x y h) :
      W.a₁ * x + W.a₃ = 0 := by
    rw [Point.neg_some, Point.some.injEq] at hT
    have h := hT.2
    simp only [negY] at h
    linear_combination -h - y * h2
  have hle : (S.erase 0).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun a ha b hb ↦ ?_
    obtain ⟨ha0, haS⟩ := Finset.mem_erase.mp ha
    obtain ⟨hb0, hbS⟩ := Finset.mem_erase.mp hb
    cases a with
    | zero => exact absurd rfl ha0
    | some x y h =>
    cases b with
    | zero => exact absurd rfl hb0
    | some x' y' h' =>
    have hx := hlin h (hS _ haS)
    have hx' := hlin h' (hS _ hbS)
    -- `a₁ = 0` would force `a₃ = 0`, and then the discriminant vanishes.
    have ha1 : W.a₁ ≠ 0 := fun h1 ↦ by
      have h3 : W.a₃ = 0 := by simpa [h1] using hx
      exact W.isUnit_Δ.ne_zero (by simp [W.Δ_of_char_two, h1, h3])
    have hxx : x = x' := mul_left_cancel₀ ha1 (by linear_combination hx - hx')
    subst hxx
    have hn : W.negY x y' = y' := by
      have h := hS _ hbS
      rw [Point.neg_some, Point.some.injEq] at h
      exact h.2
    obtain rfl : y = y' := (Y_eq_of_X_eq h.left h'.left rfl).elim id (·.trans hn)
    rfl
  have := Finset.pred_card_le_card_erase (s := S) (a := 0)
  omega

end WeierstrassCurve.Affine
