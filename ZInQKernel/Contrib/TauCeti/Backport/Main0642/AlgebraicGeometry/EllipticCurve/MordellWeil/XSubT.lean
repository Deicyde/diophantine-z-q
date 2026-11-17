/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 0642eae29e0a, module
-- TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which
-- is vendored as `ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT` (task selmer-2infty).
-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten.
module

public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.RingTheory.Polynomial.Quotient
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
public import Mathlib.Tactic.Algebra.Basic
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.Field
public import Mathlib.Tactic.LinearCombination
public import ZInQKernel.Contrib.TauCeti.Backport.Algebra.Group.MapMulMulEqOne
public import ZInQKernel.Contrib.TauCeti.Algebra.Polynomial.LinearFactor
public import ZInQKernel.Contrib.TauCeti.GroupTheory.QuotientGroup.PowMonoidHom
public import ZInQKernel.Contrib.TauCeti.RingTheory.AdjoinRoot.Basic
import ZInQKernel.Contrib.TauCeti.Algebra.Group.PowMonoidHom
import ZInQKernel.Contrib.TauCeti.Backport.Main0642.AlgebraicGeometry.EllipticCurve.Affine.Point.Collinear
import ZInQKernel.Contrib.TauCeti.RingTheory.Ideal.Quotient.Coprime
import ZInQKernel.Contrib.TauCeti.RingTheory.Polynomial.Resultant.AdjoinRoot
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.AlgebraicGeometry.EllipticCurve.Affine.Formula.AddPolynomial
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.AlgebraicGeometry.EllipticCurve.Affine.Point.Collinear

/-!
# The `x - T` map of an elliptic curve into its étale algebra

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form over a field `K`, and let `A := K[X]⧸⟨f⟩` be the étale algebra of `f`. The **descent map**,
or `x - T` map, sends a point of `W` to the square class of `x - T` in `A`, where `T` is the
class of `X`. It is the engine of the descent computing `E(K)/2E(K)`: its kernel is exactly
`2E(K)`, so `E(K)/2E(K)` embeds into a group of square classes, which is finite under the
finiteness hypotheses of the weak Mordell-Weil theorem.

The subtlety is at the `2`-torsion. If `f x ≠ 0` then `x - T` is already a unit of `A`, but at a
root `x` of `f` the element `x - T` is a zero divisor, and the map instead returns the class of
the corrected representative `x - T + fCofactor x`. Adding `fCofactor x` changes nothing modulo
`fCofactor x`, where the element still agrees with `x - T`; at the remaining factor, where
`x - T` vanishes, it takes the value `f' x`, which is nonzero because `f` is separable. That is
what makes the corrected element a unit. Both branches are packaged in `μX`, and `μ₀` extends
`μX` by sending the point at infinity to `1`.

## Main definitions

* `WeierstrassCurve.Affine.μX`, `WeierstrassCurve.Affine.μ₀`: the `x - T` map, first on
  `x`-coordinates and then on points, as a plain function.
* `WeierstrassCurve.Affine.μ`: the same map upgraded to a group homomorphism
  `Multiplicative W.Point →* W.M`.

## Main results

* `WeierstrassCurve.Affine.μ₀_mul_mul_eq_one_of_add_add_eq_zero`: the square classes of three
  collinear points multiply to `1`. This is the substance of the file, and the multiplicativity
  that makes `μ` a homomorphism; it is proved by exhibiting an explicit square root in each of
  the ways the three points can meet the `2`-torsion.
* `WeierstrassCurve.Affine.exists_eq_two_smul_iff`: a point is divisible by `2` exactly when an
  explicit polynomial identity has a solution. This is the bridge from the `x - T` map to the
  kernel computation below.
* `WeierstrassCurve.Affine.ker_μ_eq`: **the kernel of `μ` is exactly `2 • W(K)`**. This is the
  injectivity half of the descent, and the reason `W(K)/2W(K)` embeds into `W.M`. A point in the
  kernel is exhibited as `2 • P` by solving the identity of `exists_eq_two_smul_iff` from a square
  root of `x - T`, in two cases according to whether the `x`-coordinate is a root of `f`; the
  point-wise statement is `WeierstrassCurve.Affine.eq_two_smul_of_μ_eq_one`.
* `WeierstrassCurve.Affine.normM`, `WeierstrassCurve.Affine.range_μ_le_ker_normM`: the norm map
  on square classes, and **the norm condition on the image of the descent map** — every square
  class in the image of `μ` has square norm. This is what the `2`-descent tests a class against.
* `WeierstrassCurve.Affine.normM_neg_one`: the class of `-1` has norm class that of `-1`, since
  `W.A` has odd degree.
* `WeierstrassCurve.Affine.discr_f` and `WeierstrassCurve.Affine.Δ_eq_sixteen_mul_discr_f`: the
  discriminant of the cubic `f`, and `Δ = 16 · disc f`.
* `WeierstrassCurve.Affine.norm_mk_derivative_f`: the norm of `f'(T)` is `-disc f`.
* `WeierstrassCurve.Affine.discr_f_eq_mul_sq_of_eval_eq_zero`: at a root `x` of `f`, `disc f` is the
  discriminant of the cofactor `f / (X - x)` times `(f' x)²`.
* `WeierstrassCurve.Affine.norm_mk_C_sub_X_add_fCofactor`: at a root of `f`, the corrected
  representative `x - T + fCofactor x` has norm `(f' x) ^ 2`. This is the value the norm condition
  on the image of the descent map is read off from at the `2`-torsion.

The cubic quotient algebra `WeierstrassCurve.Affine.A` and its group of square classes of units
`WeierstrassCurve.Affine.M` are defined over arbitrary commutative rings. Their definitions and
the basic square-class identities do not require ellipticity or normal form. `M` is spelled as a
quotient of `W.Aˣ` by the range of Mathlib's `powMonoidHom 2`, which is the same spelling that
`TauCeti/GroupTheory/Finiteness.lean` already uses for square classes.

## Namespace

These declarations extend Mathlib's own `WeierstrassCurve.Affine` namespace rather than sitting
under `TauCeti`. That is forced by dot notation: `Affine` is a reducible abbreviation for
`WeierstrassCurve`, so `W.f` is resolved by a direct lookup on the structure's namespace and a
`TauCeti.`-prefixed copy is never found. Writing `f W` throughout instead would diverge from the
source for no gain. `TauCeti/RingTheory/AdjoinRoot/Basic.lean` sets the same precedent for a file
whose whole content extends a Mathlib namespace.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, revision `66889eada51a`),
`EllipticCurves/WeakMordellWeil.lean` lines 60-798, which are that file's Steps 2 and 3,
the divisibility criterion opening its Step 4, and Step 4 itself — the kernel computation.
The source is written against Lean `v4.32.0`; this is a forward port.

Two changes were made against the source. Stoll defines the square classes through a local
abbreviation `Units.modPow`; here they are the quotient by `(powMonoidHom 2).range` directly, so
that TauCeti carries a single spelling of square classes. In the kernel proofs this replaces the
source's `Units.modPow.unit_eq_one_iff` step by
`TauCeti.powMonoidHom_range_mk_eq_one_iff_exists_pow`, which says
the same thing about this spelling, for any commutative monoid. `norm_mk_C_sub_X_add_fCofactor`
is the source's Step 5 opening, `WeakMordellWeil.lean` lines 284-313, specialised here from the
general `AdjoinRoot.norm_mk_C_sub_X_add`, which carries that attribution. The rest of that step —
the induced norm map on square classes and the containment of the image of `μ` in its kernel — is
`WeakMordellWeil.lean` lines 873-919. It is adapted rather than copied: Stoll builds the map as
`Units.modPow.map (Algebra.norm K) 2` through his local square-class abbreviation, and the single
spelling this repo carries makes it a `QuotientGroup.map` into `Kˣ ⧸ (powMonoidHom 2).range`
instead. `discr_f` and `Δ_eq_sixteen_mul_discr_f` are the source's `discr_f` and `Δ_eq_discr_f` at
its later revision `3bfe124`; `norm_mk_derivative_f` and `discr_f_eq_mul_sq_of_eval_eq_zero` are
that revision's `norm_mk_derivative_f` (`SelmerGroup.lean`, there assuming `3 ≠ 0`) and
`discr_f_eq_discr_fCofactor_mul_sq` (`WeakMordellWeil.lean`, there through a discriminant
formula for products; here with the cofactor's discriminant written out and proved directly).
`normM_neg_one` is that revision's lemma of the same name (`SelmerGroup.lean`).
-/

public section

open Polynomial

/-!
### Commutative-ring and polynomial identities

These encode the multiplicativity of the `x - T` map on the level of coordinates, and are used
only in the proof that `μ` is a homomorphism. The polynomial ones are sign normalisations: the
representatives are naturally written `C x - X`, while `f` factors into `X - C x`, and each
rewriting step below turns one into the other.
-/

section CommRing

variable {R : Type*} [CommRing R]

/-- If `a * b * c = 0`, then `a * b + a * c + b * c` is a square root of the product of `b * c - a`
and its two analogues. -/
private lemma sq_add_add_eq_mul_mul_of_mul_mul_eq_zero {a b c : R} (h : a * b * c = 0) :
    (a * b + a * c + b * c) ^ 2 = (b * c - a) * (a * c - b) * (a * b - c) := by
  grobner

/-- If `a * d = 0` and `b * c = d - e ^ 2 * a`, then `d + e * a` is a square root of
`(d - a) * b * c`. -/
private lemma sq_add_mul_eq_mul_mul_of_mul_eq_zero {a b c d e : R} (had : a * d = 0)
    (h : b * c = d - e ^ 2 * a) : (d + e * a) ^ 2 = (d - a) * b * c := by
  grobner

/-- A corrected representative `C a - X + p`, with its linear part written as `X - C a`. -/
private lemma C_sub_X_add_eq_sub_X_sub_C (a : R) (p : R[X]) :
    C a - X + p = p - (X - C a) := by
  ring

/-- A product of three representatives `C x - X`, with every factor written as `X - C x`. -/
private lemma C_sub_X_mul_mul_eq_neg (a b c : R) :
    (C a - X) * (C b - X) * (C c - X) = -((X - C a) * (X - C b) * (X - C c)) := by
  ring

/-- A corrected representative times two plain ones, with every linear part written as
`X - C x`. -/
private lemma C_sub_X_add_mul_mul_eq_sub_mul_mul (a b c : R) (p : R[X]) :
    (C a - X + p) * (C b - X) * (C c - X) = (p - (X - C a)) * (X - C b) * (X - C c) := by
  ring

end CommRing

namespace WeierstrassCurve

namespace Affine

section CommRingCurve

variable {R : Type*} [CommRing R] (W : Affine R)

/-- In a normal form for characteristic `≠ 2`, `polynomialY` vanishes at every `(x, 0)`; at a point
of the curve this is the condition for `(x, 0)` to have order dividing two. -/
@[simp]
lemma evalEval_polynomialY_zero_eq_zero_of_isCharNeTwoNF [W.IsCharNeTwoNF] (x : R) :
    W.polynomialY.evalEval x 0 = 0 := by
  rw [evalEval_polynomialY, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  ring

/-!
### The norm at the `2`-torsion

At a root `x` of `f` the descent map uses the corrected representative `x - T + fCofactor x`, and
the norm condition on the image of the map is read off from its norm, which is a square. The
computation is `AdjoinRoot.norm_mk_C_sub_X_add`, stated there for any monic polynomial split off
a linear factor; here it is specialised to `f = fCofactor x * (X - C x)`. The other value the
condition needs, the norm of `x - T` itself on the branch where that is already a unit, is
`AdjoinRoot.norm_algebraMap_sub_root W.monic_f x`.
-/

/-! ### Square classes of the cubic quotient algebra -/

section SquareClasses

variable {W}

end SquareClasses

end CommRingCurve

section NontrivialCurve

variable {K : Type*} [CommRing K] [Nontrivial K] (W : Affine K)

end NontrivialCurve

variable {K : Type*} [Field K] (W : Affine K)

/- Dividing the relation `(r X + s)² ≡ x - X mod (fCofactor x)` by `r²` yields the polynomial
identity certifying that a point whose `x`-coordinate is a root of `f` is divisible by `2`. This
is the `2`-torsion half of `ker_μ_eq`, in the shape `exists_eq_two_smul_iff'` asks for. -/
private lemma f_dvd_of_fCofactor_dvd {x r s : K} (hx : W.f.eval x = 0) (hr : r ≠ 0)
    (hdvd : W.fCofactor x ∣ (C r * X + C s) ^ 2 - (C x - X)) :
    W.f ∣ (X - C (-s / r)) ^ 2 * (X - C x) - -(C (1 / r) * X + C (-x / r)) ^ 2 := by
  obtain ⟨q, hq⟩ := hdvd
  apply_fun (· * (X - C x)) at hq
  rw [mul_right_comm, ← f_eq_mul_of_eval_eq_zero _ hx] at hq
  replace hq : q * W.f = ((C r * X + C s) ^ 2 - (C x - X)) * (X - C x) := by
    rw [mul_comm]; exact hq.symm
  refine ⟨C (1 / r ^ 2) * q, ?_⟩
  rw [eq_comm, mul_comm W.f]
  apply_fun (C (r ^ 2) * ·) using mul_right_injective₀ <| by simp [hr]
  dsimp only
  rw [← mul_assoc, ← mul_assoc, ← map_mul]
  rw [mul_one_div_cancel <| pow_ne_zero 2 hr, map_one, one_mul, hq]
  conv_rhs =>
    rw [sub_neg_eq_add, mul_add, ← mul_assoc, map_pow, ← mul_pow, mul_sub (C r), ← map_mul,
      mul_div_cancel₀ _ hr]
    enter [2]
    rw [← mul_pow, mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hr, map_one, one_mul,
      ← map_mul, mul_div_cancel₀ _ hr]
  simp only [C_eq_algebraMap]
  algebra

variable {W}

section

variable [W.IsCharNeTwoNF]

variable [W.IsElliptic]

end

/-!
### The `x - T` map on coordinates and points
-/

variable [W.IsCharNeTwoNF]

section μX

variable [W.IsElliptic]

end μX

/- `DecidableEq K` enters here and not before: it is what Mathlib's `AddCommGroup W.Point`
instance requires, so every declaration below that mentions `W.Point` needs it. The
coordinate-level `μX` above does not mention `W.Point` and does not take it. Declared at the
outer level so that it stays in scope past the section below. -/
variable [DecidableEq K]

section μ₀

variable [W.IsElliptic]

end μ₀

/-!
### Step 3: `μ` is a homomorphism

Multiplicativity is the statement that the square classes of three collinear points multiply to
`1`. The proof splits on how many of the three `x`-coordinates are roots of `f`, i.e. on how many
of the points are `2`-torsion, and in each case exhibits an explicit square root of the product of
the three representatives.
-/

open Point in
private lemma xQ_ne_xP_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h : W.f.eval xP = 0) :
    xQ ≠ xP := by
  contrapose! hPQR
  rw! [hPQR] at hQ ⊢
  rw! [y_eq_zero_of_eval_f_eq_zero hP.1 h, y_eq_zero_of_eval_f_eq_zero hQ.1 h]
  rw [add_self_of_Y_eq <| by simp, zero_add]
  exact some_ne_zero hR

open Point in
/- If two of three collinear points have distinct `2`-torsion `x`-coordinates, then the line
through them is horizontal, and `f` splits off all three `x`-coordinates. -/
private lemma f_eq_prod_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.f = (X - C xP) * (X - C xQ) * (X - C xR) := by
  have hPQ : xQ ≠ xP := xQ_ne_xP_of_eval_f_eq_zero hP hQ hR hPQR h₁
  obtain ⟨pol, hpol, hpol₁⟩ :=
    Point.exists_polynomial_factorization_of_some_add_some_add_some_eq_zero hP hQ hR hPQR
  have hpol₀ : pol = 0 := by
    refine pol.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {xP, xQ} (fun x hx ↦ ?_) ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      apply_fun (·.eval x) at hpol
      rcases hx with rfl | rfl <;>
        rw [eval_sub, ‹eval x (f W) = 0›] at hpol <;>
        simpa using hpol
    · grind
  rwa [hpol₀, zero_pow two_ne_zero, sub_zero, eq_comm] at hpol

/- Forward direction of `exists_eq_two_smul_iff`: if `(x, y)` is divisible by `2`, then the
polynomial identity holds, with `ξ` the `x`-coordinate of a halving point. -/
private lemma exists_pol_of_eq_two_smul {x y : K} (h : W.Nonsingular x y) {P : W.Point}
    (hP : Point.some x y h = 2 • P) :
    ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  match P with
  | 0 => simp at hP -- cannot occur
  | .some ξ η h' =>
    rw [← sub_eq_zero, sub_eq_add_neg, two_smul, neg_add, ← add_assoc, add_rotate,
      Point.neg_some] at hP
    have H : W.Nonsingular ξ (W.negY ξ η) := (nonsingular_neg ξ η).mpr h'
    obtain ⟨pol, hpol, hpol₁⟩ :=
      Point.exists_polynomial_factorization_of_some_add_some_add_some_eq_zero H H h hP
    rw [← sq] at hpol
    obtain ⟨l, m, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hpol₁
    exact ⟨_, _, _, hpol⟩

variable [W.IsElliptic]

section μ₀_helper_lemmas

open Point

variable {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
  (hR : W.Nonsingular xR yR) (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0)

include hPQR

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  have hf := f_eq_prod_of_eval_f_eq_zero hP hQ hR hPQR h₁ h₂
  have h₃ : W.f.eval xR = 0 := by rw [hf]; simp
  have hfcP := W.fCofactor_eq_of_f_eq_mul (x := xP) (q := (X - C xQ) * (X - C xR))
    (by rw [hf]; ring)
  have hfcQ := W.fCofactor_eq_of_f_eq_mul (x := xQ) (q := (X - C xP) * (X - C xR))
    (by rw [hf]; ring)
  have hfcR := W.fCofactor_eq_of_f_eq_mul (x := xR) (q := (X - C xP) * (X - C xQ))
    (by rw [hf])
  rw [μX_of_eval_f_eq_zero h₁, μX_of_eval_f_eq_zero h₂, μX_of_eval_f_eq_zero h₃,
    M.mk_mul_mk_mul_mk_eq_one_iff]
  simp only [hfcP, hfcQ, hfcR, C_sub_X_add_eq_sub_X_sub_C]
  rw [map_sub, map_sub _ _ (X - C xQ), map_sub _ _ (X - C xR)]
  simp only [map_mul]
  rw [← sq_add_add_eq_mul_mul_of_mul_mul_eq_zero <| by rw [← map_mul, ← map_mul, ← hf]; simp]
  exact ⟨_, rfl⟩

/- The case where only `xP` is a `2`-torsion `x`-coordinate. -/
private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne (h : W.f.eval xP = 0)
    (hQ₀ : W.f.eval xQ ≠ 0) (hR₀ : W.f.eval xR ≠ 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rw [μX_of_eval_f_eq_zero h, μX_of_eval_f_ne_zero hQ₀, μX_of_eval_f_ne_zero hR₀,
    M.mk_mul_mk_mul_mk_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ :=
    Point.exists_polynomial_factorization_of_some_add_some_add_some_eq_zero hP hQ hR hPQR
  obtain ⟨γ, rfl⟩ : ∃ γ, pol = C γ * (X - C xP) := by
    apply_fun (·.eval xP) at hpol
    rw [eval_sub, h] at hpol
    exact exists_eq_C_mul_X_sub_C_of_natDegree_le_one hpol₁ (by simpa using hpol)
  replace hpol : (X - C xQ) * (X - C xR) =
      W.fCofactor xP - (C γ) ^ 2 * (X - C xP) := by
    apply (monic_X_sub_C xP).isRegular.left
    rw [W.f_eq_mul_of_eval_eq_zero h] at hpol
    linear_combination hpol
  simp only [← map_mul]
  rw [C_sub_X_add_mul_mul_eq_sub_mul_mul xP xQ xR (W.fCofactor xP), map_mul, map_mul, map_sub]
  rw [← sq_add_mul_eq_mul_mul_of_mul_eq_zero (e := AdjoinRoot.mk W.f (C γ)) ?H₁ ?H₂]
  case H₁ =>
    rw [← map_mul, mul_comm, ← f_eq_mul_of_eval_eq_zero W h]
    simp
  case H₂ => simp only [← map_mul, ← map_pow, ← map_sub, hpol]
  exact ⟨_, rfl⟩

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero (h : W.f.eval xP = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  by_cases hQ₀ : W.f.eval xQ = 0
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hQ hR hPQR h hQ₀
  by_cases hR₀ : W.f.eval xR = 0
  · rw [mul_right_comm]
    rw [add_right_comm] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hR hQ hPQR h hR₀
  exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne hP hQ hR hPQR h hQ₀ hR₀

end μ₀_helper_lemmas

/-!
### The divisibility criterion

What belongs here is the criterion the kernel computation runs on, namely that divisibility by
`2` is equivalent to an explicit polynomial identity. `exists_eq_two_smul_iff'` restates it inside
`W.A`, which is the form the square-class argument consumes; the section below runs that argument
and concludes in `ker_μ_eq`.
-/

/- Reverse direction of `exists_eq_two_smul_iff`, in terms of the coefficient identities of
the polynomial identity: the point `(ξ, lξ + m)` lies on `W` and doubles to `(x, ±y)`. -/
private lemma exists_eq_two_smul_of_identities {x y ξ l m : K} (h : W.Nonsingular x y)
    (H₂ : x + 2 * ξ = l ^ 2 - W.a₂) (H₁ : 2 * x * ξ + ξ ^ 2 = W.a₄ - 2 * l * m)
    (H₀ : x * ξ ^ 2 = -W.a₆ + m ^ 2) :
    ∃ P, Point.some x y h = 2 • P := by
  have h20 : (2 : K) ≠ 0 := Ring.two_ne_zero <| ringChar_ne_two W
  have heq : W.Equation ξ (l * ξ + m) := by
    rw [equation_iff_eval_f_eq_sq, eval_f]
    linear_combination ξ ^ 2 * H₂ - ξ * H₁ + H₀
  have hy₀ : l * ξ + m ≠ 0 := by
    intro hzero
    have hx : W.f.eval ξ = 0 := by
      simpa [hzero] using (equation_iff_eval_f_eq_sq W ξ (l * ξ + m)).mp heq
    apply W.deriv_f_ne_zero hx
    linear_combination 2 * l * hzero + 2 * ξ * H₂ - H₁
  have hy : l * ξ + m ≠ W.negY ξ (l * ξ + m) := by
    rw [negY_of_isCharNeTwoNF]
    grind
  have hsl : W.slope ξ ξ (l * ξ + m) (l * ξ + m) = l := by
    simp only [slope_of_Y_ne rfl hy, a₁_of_isCharNeTwoNF, zero_mul, sub_zero,
      negY_of_isCharNeTwoNF, sub_neg_eq_add, ← two_mul]
    rw [mul_comm] at hy₀ -- `field_simp` changes `l * ξ` to `ξ * l`
    field_simp
    grobner
  let P : W.Point := .some ξ (l * ξ + m) <| equation_iff_nonsingular.mp heq
  suffices .some x y h = 2 • P ∨ .some x y h = 2 • (-P) from this.casesOn (⟨_, ·⟩) (⟨_, ·⟩)
  simp only [smul_neg, P, two_smul, Point.add_self_of_Y_ne hy, ← Point.X_eq_iff, hsl, addX,
    a₁_of_isCharNeTwoNF, zero_mul, add_zero]
  linear_combination H₂

/-!
### The kernel of the `x - T` map

Both inclusions of `ker_μ_eq`. That `2 • P` is killed is `μ₀_two_nsmul`; the converse is trivial at
the point at infinity and, at an affine point, splits on whether `f` vanishes at the `x`-coordinate.
Each affine branch feeds the criterion of the previous section a square root extracted from
`μ (some x y h) = 1`.
-/

section kernel

variable {x y : K} (h : W.Nonsingular x y)

include h

private lemma eq_two_smul_of_μ_eq_one_of_ne (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x ≠ 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_ne_zero hx,
    TauCeti.powMonoidHom_range_mk_eq_one_iff_exists_pow,
    IsUnit.unit_spec] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨r, s, t, hrst⟩ := W.exists_mk_quadratic_eq z
  rw [hrst] at hz
  have hr : r ≠ 0 := by
    intro rfl
    simp only [map_zero, zero_mul, zero_add, ← map_pow] at hz
    rw [AdjoinRoot.mk_eq_mk_iff_of_degree_lt W.monic_f
      (W.degree_lt_degree_f (by compute_degree!))
      (W.degree_lt_degree_f (by compute_degree!))] at hz
    apply_fun natDegree at hz
    rw [natDegree_pow, natDegree_C_sub_X] at hz
    lia
  obtain ⟨ξ, l, m, H⟩ := W.exists_X_sub_C_mul_eq r s t hr
  rw [← map_mul] at H
  refine ⟨ξ, l, m, ?_⟩
  apply_fun (fun p ↦ AdjoinRoot.mk W.f (X - C ξ) ^ 2 * p) at hz
  rw [← neg_inj, eq_comm, ← map_pow, ← map_mul, ← map_neg] at hz
  conv_rhs at hz => rw [← map_pow, ← map_mul, ← mul_pow, map_pow, H, ← map_pow, ← map_neg]
  convert hz
  ring

private lemma eq_two_smul_of_μ_eq_one_of_eq (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x = 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_eq_zero hx,
    TauCeti.powMonoidHom_range_mk_eq_one_iff_exists_pow,
    IsUnit.unit_spec] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨r, s, hrs⟩ := W.exists_mk_linear_eq (AdjoinRoot.mk (W.fCofactor x) p)
  rw [← hp, ← map_pow, AdjoinRoot.mk_eq_mk] at hz
  have hz' : AdjoinRoot.mk (W.fCofactor x) (p ^ 2) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X + W.fCofactor x) :=
    AdjoinRoot.mk_eq_mk.mpr <| dvd_trans ⟨X - C x, W.f_eq_mul_of_eval_eq_zero hx⟩ hz
  rw [map_pow, hrs, map_add _ _ (W.fCofactor x), AdjoinRoot.mk_self, add_zero] at hz'
  have hr₀ : r ≠ 0 := by
    intro rfl
    rw [map_zero, zero_mul, zero_add, ← map_pow,
      AdjoinRoot.mk_eq_mk_iff_of_degree_lt (W.monic_fCofactor x)
        (W.degree_lt_degree_fCofactor x (by compute_degree!))
        (W.degree_lt_degree_fCofactor x (by compute_degree!))] at hz'
    apply_fun natDegree at hz'
    rw [natDegree_pow, natDegree_C_sub_X] at hz'
    lia
  rw [← map_pow, AdjoinRoot.mk_eq_mk] at hz'
  exact ⟨-s / r, 1 / r, -x / r, AdjoinRoot.mk_eq_mk.mpr (W.f_dvd_of_fCofactor_dvd hx hr₀ hz')⟩

end kernel

/-!
### The norm map on square classes

`Algebra.norm K : W.A →* K` carries units to units and squares to squares, so it descends to the
square classes: `normM` sends the class of `u : W.Aˣ` to the class of its norm in
`Kˣ ⧸ (powMonoidHom 2).range`, the ambient of Mathlib's Selmer group. Both branches of `μX` have
square norm — off the `2`-torsion the norm of `x - T` is `f x`, which the curve equation makes
`y ^ 2`, and at a root of `f` the norm of the corrected representative is `(f' x) ^ 2` — so the
image of `μ` lies in the kernel of `normM`. That containment is the norm condition the `2`-descent
reads off the image of the descent map.
-/

section normM

end normM

end Affine

end WeierstrassCurve

end
