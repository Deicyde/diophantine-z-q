/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 0642eae29e0a, module
-- TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.LocalCondition), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which
-- is vendored as `ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.LocalCondition` (task selmer-2infty).
-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten.
module

public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.MordellWeil.LocalCondition
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.AlgebraicGeometry.EllipticCurve.MordellWeil.XSubT
public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.NormalForms
public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.BaseChange
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.AlgebraicGeometry.EllipticCurve.Affine.Formula.AddPolynomial
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.AlgebraicGeometry.EllipticCurve.Affine.Point.Collinear

/-!
# Base change of the étale algebra, and the local condition of `2`-descent

Let `W : y² = f(x) = x³ + a₂x² + a₄x + a₆` be an elliptic curve in characteristic `≠ 2` normal
form over a field `K`, with étale algebra `A = K[X]⧸⟨f⟩` and descent map
`μ : W(K) → M = Aˣ/(Aˣ)²`, as set up in
`TauCeti/AlgebraicGeometry/EllipticCurve/MordellWeil/XSubT.lean`.

Everything in that construction base-changes along a field extension `L/K` — in the arithmetic
application `L` is a completion of `K`. This file builds that base change and uses it to define
the **local condition** at `L`: the subgroup

`W.localCondition L : Subgroup W.M`

of square classes whose image in `(W⁄L).M` lies in the image of the local descent map `μ_L`. The
`2`-Selmer group of `W` is cut out of `W.M` by these conditions at all completions of `K`, so
`localCondition` is the object every later descent statement is phrased in.

The underlying cubic quotient algebra, its square-class group, and their base-change maps are
defined over arbitrary commutative rings. The discriminant identity holds at this generality
as well, and a root of the cubic gives a nonsingular point after base change to any nontrivial
commutative algebra, provided the curve is elliptic and in characteristic-≠-2 normal form.

## Main definitions

* `WeierstrassCurve.Affine.mapA`: the base-change homomorphism `R[X]⧸⟨f⟩ →+* S[X]⧸⟨f⟩` of
  cubic quotient algebras, which are étale in the elliptic characteristic-≠-2 setting.
* `WeierstrassCurve.Affine.localRes`: the induced map `W.M →* (W⁄S).M` on square classes over
  commutative rings.
* `WeierstrassCurve.Affine.localCondition`: the local `2`-descent condition at `L`.

## Main statements

* `WeierstrassCurve.Affine.baseChange_discr_f`: the discriminant of the cubic `f` commutes with
  base change.
* `WeierstrassCurve.Affine.nonsingular_baseChange_of_aeval_eq_zero`: a root `x` of `f` in a
  nontrivial algebra `S` gives the point `(x, 0)` of `W⁄S`.
* `WeierstrassCurve.Affine.localRes_μX` and `WeierstrassCurve.Affine.localRes_comp_μ`: the
  descent map is natural under base change — restricting square classes after the global `μ` is
  applying the local `μ` after the base change of points.
* `WeierstrassCurve.Affine.range_μ_le_localCondition`: the image of the global descent map
  satisfies the local condition at every extension field. This is what makes `localCondition` a
  *condition*: it is a constraint the classes coming from `W(K)` are known to satisfy, so the
  intersection of the local conditions bounds `W(K)/2W(K)` from above.
* `WeierstrassCurve.Affine.card_range_μ_of_surjective_algebraMap`: base change along an
  *isomorphism* preserves the size of the descent image, via
  `WeierstrassCurve.Affine.range_μ_of_surjective_algebraMap`, which identifies the two images.
  This is the transport step: a count of `#(im μ)` established over a concrete field carries to
  any field isomorphic to it. Its inputs are
  `WeierstrassCurve.Affine.bijective_mapA_of_bijective_algebraMap` and
  `WeierstrassCurve.Affine.localRes_bijective_of_bijective_algebraMap`.

## Implementation notes

Square classes are spelled `W.M`, the quotient of `W.Aˣ` by the range of `powMonoidHom 2`,
following `XSubT.lean`; the source uses a local abbreviation `Units.modPow` for the same group,
which is not a Mathlib declaration and which TauCeti deliberately does not carry, so that the
repository has a single spelling of square classes. Accordingly `localRes` is built from
`QuotientGroup.map` rather than from the source's `Units.modPow.map`.

The base change of points is `WeierstrassCurve.Affine.pointMap`, from
`TauCeti/AlgebraicGeometry/EllipticCurve/Affine/BaseChange.lean`.

## Provenance

Adapted, with the author's proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, revision `66889eada51a`),
`EllipticCurves/SelmerGroup.lean` lines 85-323 — that file's `BaseChange` section: lines 85-295
give the base change up to the local condition and its compatibility with `μ`, and lines 296-323
give the isomorphism-invariance block — `range_μ_of_bijective_algebraMap` and
`card_range_μ_of_bijective_algebraMap` upstream, renamed here for the weaker hypothesis — plus the
étale-algebra bijectivity at line 168.

The square-class isomorphism statement `localRes_bijective_of_bijective_algebraMap` follows from
`QuotientGroup.congrRangePowMonoidHom` applied to the induced equivalence of unit groups.
`baseChange_discr_f` is the source's lemma of that name at its later revision `3bfe124`.
`nonsingular_baseChange_of_aeval_eq_zero` is not from the source: it is
`WeierstrassCurve.Affine.nonsingular_of_eval_f_eq_zero` after base change.
-/

public section

open Polynomial

namespace WeierstrassCurve

namespace Affine

section CommRing

variable {R : Type*} [Field R] (W : Affine R)

section Map

variable {S : Type*} [CommRing S] (σ : R →+* S)

end Map

section Algebra

variable (S : Type*) [Field S] [Algebra R S]

variable {S} in
/-- A root `x` of the cubic `f` in a nontrivial `R`-algebra `S` gives the nonsingular point
`(x, 0)` of the base-changed curve `W⁄S`. -/
lemma nonsingular_baseChange_of_aeval_eq_zero [Nontrivial S] [W.IsElliptic] [W.IsCharNeTwoNF]
    {x : S} (hx : aeval x W.f = 0) : (W⁄S).toAffine.Nonsingular x 0 :=
  (W⁄S).toAffine.nonsingular_of_eval_f_eq_zero <| by
    rw [W.baseChange_f, eval_map_algebraMap, hx]


end Algebra

end CommRing

variable {K : Type*} [Field K] (W : Affine K)

section BaseChange

variable (L : Type*) [Field L] [Algebra K L]

variable [W.IsElliptic] [W.IsCharNeTwoNF]

/-!
### Base change along an isomorphism

If `L/K` is an isomorphism rather than a proper extension, nothing is lost: the étale algebras
are isomorphic, so the descent map has the same image over `L` as over `K`. This is what lets a
count established over a concrete field — `ℝ`, say — be transported to a completion that is
merely isomorphic to it.
-/

end BaseChange

end Affine

end WeierstrassCurve

end
