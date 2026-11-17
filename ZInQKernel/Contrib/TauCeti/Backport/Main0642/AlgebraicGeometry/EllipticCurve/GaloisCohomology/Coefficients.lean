/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 0642eae29e0a, module
-- TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Coefficients), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which
-- is vendored as `ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Coefficients` (task selmer-2infty).
-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten.
module

public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Coefficients
public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Galois
public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong
public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Surjective
public import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic
public import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.ShortExact
public import ZInQKernel.Contrib.TauCeti.Topology.Algebra.GroupAction.ForcedDiscrete
public import ZInQKernel.Contrib.TauCeti.Topology.Algebra.GroupAction.QuotientAddGroup
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
-- Proof-only: finiteness of the torsion of an elliptic curve.
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.KernelCard

-- Non-public: the nonvanishing of `m` in `Kˢ` is used only inside proofs.
import ZInQKernel.Contrib.TauCeti.Algebra.Algebra.NatCast
-- Proof-only: a `ZMod 2`-module of cardinality four is a Klein four-group.
import ZInQKernel.Contrib.TauCeti.Algebra.Group.ElementaryTwoQuotient.KleinFour
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion

/-!
# The Galois coefficient modules of an elliptic curve

Let `W` be a Weierstrass curve over a field `K`, `Kˢ` a separable closure of `K` and
`G_K = AbsoluteGaloisGroup K`. The Galois cohomology of an elliptic curve takes its coefficients
in two discrete `G_K`-modules, fixed here once and for all:

```text
W.PointCoeff = E(Kˢ),      W.TorsionCoeff m = E(Kˢ)[m],
```

with `G_K` acting on the coordinates of points. The first is a type synonym of
`TauCeti.ForcedDiscrete` applied to the points of the base change `W⁄Kˢ`, so it carries the
**discrete** topology imposed by that wrapper rather than by an instance on the point type
itself. Both modules are discrete `G_K`-modules in the sense continuous cohomology
asks for: the stabilizer of a point is open, because its coordinates lie in `Kˢ`, which is
algebraic over `K` (`WeierstrassCurve.PointCoeff.instContinuousSMul`).

For `m` invertible in `K`, multiplication by `m` gives the **Kummer sequence** of `W`,

```text
0 ⟶ E(Kˢ)[m] ⟶ E(Kˢ) ⟶ E(Kˢ) ⟶ 0,
```

as a `TauCeti.ContCohomology.DiscreteShortExact` (`WeierstrassCurve.kummerShortExact`), so that the
long exact sequence of continuous cohomology applies to it verbatim. Exactness on the right is the
divisibility of `E(Kˢ)` (`WeierstrassCurve.Affine.nsmul_surjective`), which is where invertibility
of `m` enters.

Finally `WeierstrassCurve.basePointEquivInvariants` identifies `H⁰(G_K, E(Kˢ))` with `E(K)`. The
two are different Lean types, so what is supplied is the canonical isomorphism, induced by the
inclusion `K → Kˢ`. It rests on the fixed field of `G_K` being `K`, which is why the separable
closure and not an algebraic closure is used: over an imperfect `K` the points of `E` fixed by the
automorphisms of an algebraic closure are the points over the perfect closure of `K`.

## Main definitions

* `WeierstrassCurve.PointCoeff`: the points of `W` over `Kˢ`, as a discrete `G_K`-module.
* `WeierstrassCurve.pointCoeffEquiv`: its identification with the points of `W⁄Kˢ`.
* `WeierstrassCurve.TorsionCoeff`: the `m`-torsion of `W.PointCoeff`, a discrete `G_K`-module.
* `WeierstrassCurve.torsionCoeffIncl`: the equivariant inclusion `E(Kˢ)[m] → E(Kˢ)`.
* `WeierstrassCurve.kummerShortExact`: the Kummer sequence `0 → E[m] → E → E → 0` of `W`.
* `WeierstrassCurve.basePointCoeff`: the inclusion `E(K) → E(Kˢ)`, the transport of points along
  `K → Kˢ` (`WeierstrassCurve.basePointCoeff_eq_pointCoeffEquiv_mapAlong`).
* `WeierstrassCurve.basePointEquivInvariants`: the isomorphism `E(K) ≅ H⁰(G_K, E(Kˢ))`.
* `WeierstrassCurve.baseTorsionCoeff`: the inclusion `E(K)[m] → E(Kˢ)[m]`.

## Main results

* `WeierstrassCurve.PointCoeff.instContinuousSMul`,
  `WeierstrassCurve.TorsionCoeff.instContinuousSMul`: the coefficients are discrete modules.
* `WeierstrassCurve.finite_torsionCoeff`: `E(Kˢ)[m]` is finite for `W` elliptic and `m ≠ 0`.
* `WeierstrassCurve.pointGaloisAction_apply_eq_smul`: the action is
  `WeierstrassCurve.pointGaloisAction`, and
  `WeierstrassCurve.torsionByCongr_pointCoeffEquiv_symm_smul` its torsion counterpart
  `WeierstrassCurve.torsionGaloisAction`.
* `WeierstrassCurve.Affine.Point.map_map_separableClosure_val`: an automorphism of `K^{alg}` acts
  on the points of `E(Kˢ)` through its restriction to `Kˢ`.
* `WeierstrassCurve.natCard_torsionCoeff`: `E(Kˢ)[m]` has `m²` points for `m` invertible in `K`.
* `WeierstrassCurve.isAddKleinFour_torsionCoeff_two`: `E(Kˢ)[2]` is a Klein four-group.
* `WeierstrassCurve.cast_pointCoeff_smul`, `WeierstrassCurve.cast_torsionCoeff_smul`: transport of
  the coefficients along an equality of curves, such as `(W⁄L)⁄M = W⁄M`, is `G_K`-equivariant.
* `WeierstrassCurve.mem_H0_pointCoeff_iff`: a point of `E(Kˢ)` fixed by `G_K` comes from `E(K)`,
  and `WeierstrassCurve.exists_baseTorsionCoeff_eq_of_forall_smul_eq` its torsion counterpart.

## Implementation notes

The construction follows the multiplicative coefficient modules of
`TauCeti/FieldTheory/GaloisCohomology/Coefficients.lean`: `WeierstrassCurve.PointCoeff`,
`WeierstrassCurve.kummerShortExact` and `WeierstrassCurve.basePointEquivInvariants` play the roles
of `TauCeti.UnitsCoeff`, `TauCeti.kummerShortExact` and `TauCeti.baseUnitsEquivInvariants` there.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], VIII.2 and X.4.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

/-! ### The points over the separable closure -/

/-! ### The Galois action -/

open scoped Classical in
variable {W} in
/-- **Restriction to `Kˢ` commutes with the point map into `K^{alg}`.** An automorphism `σ` of
`K^{alg}` acts on the image in `E(K^{alg})` of a point of `E(Kˢ)` as its restriction to `Kˢ` acts
on that point. -/
theorem Affine.Point.map_map_separableClosure_val (σ : Gal(AlgebraicClosure K/K))
    (Q : (W⁄(SeparableClosure K)).toAffine.Point) :
    Affine.Point.map σ.toAlgHom (Affine.Point.map (separableClosure K (AlgebraicClosure K)).val Q) =
      Affine.Point.map (separableClosure K (AlgebraicClosure K)).val
        (Affine.Point.map (absoluteGaloisGroupRestrictEquiv K σ).toAlgHom Q) := by
  have h : σ.toAlgHom.comp (separableClosure K (AlgebraicClosure K)).val =
      (separableClosure K (AlgebraicClosure K)).val.comp
        (absoluteGaloisGroupRestrictEquiv K σ).toAlgHom :=
    AlgHom.ext fun x ↦ (coe_absoluteGaloisGroupRestrictEquiv_apply K σ x).symm
  rw [Affine.Point.map_map, h, ← Affine.Point.map_map]

/-! ### The `m`-torsion -/

/-- **`E(Kˢ)[2]` is a Klein four-group** when `2` is invertible in `K`: it has `2² = 4` points,
each killed by `2`. -/
theorem isAddKleinFour_torsionCoeff_two [W.IsElliptic] (h2 : IsUnit ((2 : ℕ) : K)) :
    IsAddKleinFour (W.TorsionCoeff 2) :=
  letI := AddSubgroup.torsionBy.zmodModule (A := W.PointCoeff) (n := 2)
  TauCeti.isAddKleinFour_of_natCard_eq_four (natCard_torsionCoeff W h2)

/-! ### Transport along an equality of curves -/

section Cast

variable {V V' : WeierstrassCurve K} (h : V = V')

end Cast

/-! ### The Kummer sequence -/

/-! ### The invariants of `E(Kˢ)` -/

variable [DecidableEq K]

open scoped Classical in
/-- The inclusion of rational torsion agrees with transport along the base-field embedding. -/
theorem torsionByCongr_symm_baseTorsionCoeff (m : ℕ)
    (P : AddSubgroup.torsionBy W.toAffine.Point m) :
    (AddEquiv.torsionByCongr W.pointCoeffEquiv m).symm (W.baseTorsionCoeff m P) =
      W.torsionMapAlong (algebraMap K (SeparableClosure K)) m P := by
  apply Subtype.ext
  simp only [AddEquiv.torsionByCongr_symm_apply_coe, WeierstrassCurve.coe_baseTorsionCoeff,
    WeierstrassCurve.coe_torsionMapAlong_apply,
    WeierstrassCurve.basePointCoeff_eq_pointCoeffEquiv_mapAlong]
  -- `mapAlong` targets `W.map`, whereas the coefficient equivalence uses `W⁄Kˢ`.
  exact W.pointCoeffEquiv.symm_apply_apply _

end WeierstrassCurve
