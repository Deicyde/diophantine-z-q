/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 0642eae29e0a, module
-- TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.TwoDescent), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which
-- is vendored as `ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.TwoDescent` (task selmer-2infty).
-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten.
module

public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.TwoDescent
public import ZInQKernel.Contrib.TauCeti.Algebra.Algebra.NatCast
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion
public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Descent
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Basic
public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.FieldTheory.GaloisCohomology.Kummer
public import ZInQKernel.Contrib.TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Tower
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Coefficients
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.FieldTheory.Galois.AbsoluteGaloisGroup.Norm
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.FieldTheory.GaloisCohomology.Units.CoeffMap

/-!
# The Kummer map of multiplication by two is `x - e`

Let `W` be an elliptic curve over a field `K` in which `2` is invertible, and let `T = (e, t)` be a
point of `W(K)` of order two. The Kummer map of `[2]` sends `P ∈ E(K)` to a class in
`H¹(G_K, E[2])`, and the character `E[2] → μ₂` which is trivial exactly on `{O, T}` carries it to
`H¹(G_K, μ₂) = Kˣ ⧸ (Kˣ)²`. This file proves that the result is the square class of `x(P) - e`
(Silverman X.1.4):

```text
H¹(G_K, E[2]) ⟶ H¹(G_K, μ₂),      δ(P) ↦ class of x(P) - e,
```

with the conventions that `O` goes to `1` and `T` itself, where `x - e` vanishes, goes to
`c_T = -W_X(e, t) = 3e² + 2a₂e + a₄ - a₁t`, which is `(e - e')(e - e'')` when the equation is
`y² = (x - e)(x - e')(x - e'')`. The character `E[2] → μ₂` is the Weil pairing `e₂(·, T)`
(`WeierstrassCurve.twoTorsionCharacter_eq_weilPairing`): the `2`-torsion of `E(Kˢ)` has four
points, and `e₂(S, T) = 1` exactly for `S ∈ {O, T}`.

This identifies the explicit `x - e` map of the `2`-descent with the cohomological Kummer map,
read through `T`. Applied over an extension `L` of `K` containing a root `e` of the `2`-division
polynomial, together with the compatibility of the Kummer map with restriction to `L`
(`WeierstrassCurve.torsionRes_kummerMap`), it computes the component at `e` of the comparison
between the cohomological Kummer map and the explicit `x - θ` map into the square classes of the
étale algebra of that polynomial; it is one ingredient of the comparison of the two `2`-Selmer
groups, not that comparison itself.

The computation is the classical one. Choose `Q ∈ E(Kˢ)` with `2Q = P`. If `P ∉ {O, T}`, then
`ψ₂(Q) ≠ 0` and `x(P) - e = α²` with `α = ((x(Q) - e)² - c_T) / ψ₂(Q)`
(`WeierstrassCurve.Affine.Point.xCoord_add_self_sub_mul_sq`). If `P = T`, then `c_T = α²` with
`α = x(Q) - e`. In both cases `σ α = α` when `σ Q - Q ∈ {O, T}` and `σ α = -α` otherwise, by the
formulas for translation by a point of order two
(`WeierstrassCurve.Affine.Point.sq_xCoord_add_sub_add_evalEval_polynomialX_div` and
`WeierstrassCurve.Affine.Point.xCoord_add_sub`). So the Kummer cocycle `σ ↦ σ α / α` of the
unit is the image of the Kummer cocycle `σ ↦ σ Q - Q` of `P`.

## Main definitions

* `WeierstrassCurve.twoTorsionCoeff`: the point `T`, as an element of `E(Kˢ)[2]`.
* `WeierstrassCurve.twoTorsionCharacter`: the character `E(Kˢ)[2] → μ₂`, trivial exactly on
  `{O, T}`, as a homomorphism of `G_K`-modules.
* `WeierstrassCurve.twoDescentUnit`: the map `E(K) → Kˣ` sending `P` to `x(P) - e`, with `O ↦ 1`
  and `T ↦ c_T`.

## Main results

* `WeierstrassCurve.coe_toMul_twoTorsionCharacter`: the character is `1` on `{O, T}` and `-1` off
  it.
* `WeierstrassCurve.twoTorsionCharacter_eq_weilPairing`: the character is `e₂(·, T)`.
* `WeierstrassCurve.twoTorsionCharacter_eq_weilPairingCoeff`: the same, as an equality with the
  coefficient map `WeierstrassCurve.weilPairingCoeff` of `T`.
* `WeierstrassCurve.explicitMap1_explicitCoeff1_twoTorsionCharacter_torsionRes`: the character
  is natural under change of field.
* `WeierstrassCurve.kummerIso_powerClassMap_of_kummerIso_eq`: the same naturality, read through
  the Kummer isomorphism on power classes.
* `WeierstrassCurve.explicitCoeff1_twoTorsionCharacter_kummerMap`: the image of the Kummer class of
  `P` under the character is the Kummer class of `x(P) - e`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1.4.
-/

public section

noncomputable section

open TauCeti TauCeti.ContCohomology

namespace WeierstrassCurve

/-! ### The character `E(Kˢ)[2] → μ₂` attached to `T` -/

section Character

open WeierstrassCurve.Affine.Point

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) {e t : K}
  (hT : W.toAffine.Nonsingular e t) (hψ : W.toAffine.polynomialY.evalEval e t = 0)


/-- **`twoTorsionCharacter` is the coefficient map `WeierstrassCurve.weilPairingCoeff` of `T`**,
the bundled form of `WeierstrassCurve.twoTorsionCharacter_eq_weilPairing`. -/
theorem twoTorsionCharacter_eq_weilPairingCoeff [W.IsElliptic] (h2 : IsUnit ((2 : ℕ) : K)) :
    W.twoTorsionCharacter hT hψ h2 =
      W.weilPairingCoeff 2 h2 ⟨some e t hT, Affine.Point.some_mem_torsionBy_two hT hψ⟩ := by
  ext S
  have hT2 : W.twoTorsionCoeff hT hψ =
      W.baseTorsionCoeff 2 ⟨some e t hT, Affine.Point.some_mem_torsionBy_two hT hψ⟩ :=
    Subtype.ext ((W.coe_twoTorsionCoeff hT hψ).trans (W.coe_baseTorsionCoeff ⟨some e t hT, Affine.Point.some_mem_torsionBy_two hT hψ⟩).symm)
  rw [twoTorsionCharacter_eq_weilPairing, weilPairingCoeff_apply, hT2]

end Character

/-! ### Naturality of the character under change of field -/

section ChangeOfField

variable {K : Type*} [Field K] (W : WeierstrassCurve K)

private theorem explicitCoeff1_twoTorsionCharacter_cast {M : Type*} [Field M] [DecidableEq M]
    {V V' : WeierstrassCurve M} (h : V = V') [V.IsElliptic] [V'.IsElliptic] {e : M}
    (hT : V.toAffine.Nonsingular e 0) (hψ : V.toAffine.polynomialY.evalEval e 0 = 0)
    (hT' : V'.toAffine.Nonsingular e 0) (hψ' : V'.toAffine.polynomialY.evalEval e 0 = 0)
    (h2 : IsUnit ((2 : ℕ) : M)) (x : H1 (AbsoluteGaloisGroup M) (V.TorsionCoeff 2)) :
    explicitCoeff1 _ _ (V'.twoTorsionCharacter hT' hψ' h2) continuous_of_discreteTopology
        (explicitCoeff1Equiv _ _
          (AddEquiv.cast (M := fun V : WeierstrassCurve M ↦ V.TorsionCoeff 2) h)
          continuous_of_discreteTopology continuous_of_discreteTopology
          (cast_torsionCoeff_smul h) x) =
      explicitCoeff1 _ _ (V.twoTorsionCharacter hT hψ h2) continuous_of_discreteTopology x := by
  subst h
  -- after `subst`, the transport is the identity on cocycles: `AddEquiv.cast rfl` is the identity
  -- by definition, which is what the final `rfl` uses
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    rw [explicitCoeff1Equiv_mk]
    exact congrArg (explicitCoeff1 _ _ _ _) (congrArg _ (Subtype.ext (funext fun g ↦
      (cocyclesMap1_apply _ _ _ _ _ _ _ _ z g).trans rfl)))

/-- **The character in a tower**: restriction along a tower `K → F → M`, followed by the transport
of `E[2]` from `(W⁄F)⁄M` to `W⁄M`, carries the character `e₂(·, (e, 0))` of `(W⁄F)⁄M` to the
character at the same point of `W⁄M`, after restriction from `K` to `M`. -/
theorem explicitCoeff1_twoTorsionCharacter_torsionRes_torsionRes [W.IsElliptic]
    {F : Type*} [Field F] [Algebra K F]
    {M : Type*} [Field M] [Algebra K M] [Algebra F M] [IsScalarTower K F M] [DecidableEq M]
    (τ₁ : SeparableClosure K →ₐ[K] SeparableClosure F)
    (τ' : SeparableClosure F →ₐ[F] SeparableClosure M)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure M) {e : M}
    (hT : ((W.baseChange F).baseChange M).toAffine.Nonsingular e 0)
    (hψ : ((W.baseChange F).baseChange M).toAffine.polynomialY.evalEval e 0 = 0)
    (hT' : (W.baseChange M).toAffine.Nonsingular e 0)
    (hψ' : (W.baseChange M).toAffine.polynomialY.evalEval e 0 = 0)
    (h2M : IsUnit ((2 : ℕ) : M)) (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) :
    explicitCoeff1 _ _ (((W.baseChange F).baseChange M).twoTorsionCharacter hT hψ h2M)
        continuous_of_discreteTopology ((W.baseChange F).torsionRes τ' 2 (W.torsionRes τ₁ 2 c)) =
      explicitCoeff1 _ _ ((W.baseChange M).twoTorsionCharacter hT' hψ' h2M)
        continuous_of_discreteTopology (W.torsionRes τ 2 c) := by
  rw [W.torsionRes_torsionRes τ₁ τ' τ]
  exact explicitCoeff1_twoTorsionCharacter_cast _ hT' hψ' hT hψ h2M _

/-- **Naturality of the character under change of field**: restriction from `F` to `M` carries
the image of a class under the character `e₂(·, (e, 0))` over `F` to the image under the
character at `(e, 0)` over `M`, both after restriction from `K`. -/
theorem explicitMap1_explicitCoeff1_twoTorsionCharacter_torsionRes [W.IsElliptic]
    {F : Type*} [Field F] [Algebra K F] [DecidableEq F]
    {M : Type*} [Field M] [Algebra K M] [Algebra F M] [IsScalarTower K F M] [DecidableEq M]
    (τ₁ : SeparableClosure K →ₐ[K] SeparableClosure F)
    (τ' : SeparableClosure F →ₐ[F] SeparableClosure M)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure M) {e : F}
    (hT : (W.baseChange F).toAffine.Nonsingular e 0)
    (hψ : (W.baseChange F).toAffine.polynomialY.evalEval e 0 = 0)
    (hT' : (W.baseChange M).toAffine.Nonsingular (algebraMap F M e) 0)
    (hψ' : (W.baseChange M).toAffine.polynomialY.evalEval (algebraMap F M e) 0 = 0)
    (h2F : IsUnit ((2 : ℕ) : F)) (h2M : IsUnit ((2 : ℕ) : M))
    (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) :
    explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ') (kummerCoeffBaseChange 2 τ')
        continuous_of_discreteTopology (kummerCoeffBaseChange_smul 2 τ')
        (explicitCoeff1 _ _ ((W.baseChange F).twoTorsionCharacter hT hψ h2F)
          continuous_of_discreteTopology (W.torsionRes τ₁ 2 c)) =
      explicitCoeff1 _ _ ((W.baseChange M).twoTorsionCharacter hT' hψ' h2M)
        continuous_of_discreteTopology (W.torsionRes τ 2 c) := by
  have hTM : ((W.baseChange F).baseChange M).toAffine.Nonsingular (algebraMap F M e) 0 := by
    have := ((W.baseChange F).toAffine.map_nonsingular (algebraMap F M).injective e 0).mpr hT
    rwa [_root_.map_zero] at this
  have hψM :
      ((W.baseChange F).baseChange M).toAffine.polynomialY.evalEval (algebraMap F M e) 0 = 0 :=
    (show W.baseChange M = (W.baseChange F).baseChange M from
      (W.map_baseChange (IsScalarTower.toAlgHom K F M)).symm) ▸ hψ'
  -- the point `(e, 0)` of `W⁄F` goes to the point `(e, 0)` of `(W⁄F)⁄M`
  have hTT : (⟨.some (algebraMap F M e) 0 hTM, Affine.Point.some_mem_torsionBy_two hTM hψM⟩ :
        AddSubgroup.torsionBy ((W.baseChange F).baseChange M).toAffine.Point (2 : ℕ)).val =
      (W.baseChange F).toAffine.pointMap M (⟨.some e 0 hT,
        Affine.Point.some_mem_torsionBy_two hT hψ⟩ :
        AddSubgroup.torsionBy (W.baseChange F).toAffine.Point (2 : ℕ)).val := by
    simp only [Affine.pointMap_some, _root_.map_zero]
  rw [twoTorsionCharacter_eq_weilPairingCoeff,
    explicitMap1_explicitCoeff1_weilPairingCoeff (W.baseChange F) 2 h2F τ' hTT,
    ← twoTorsionCharacter_eq_weilPairingCoeff _ hTM hψM]
  exact explicitCoeff1_twoTorsionCharacter_torsionRes_torsionRes W τ₁ τ' τ hTM hψM hT' hψ' h2M c

/-- **Naturality of the character, on power classes**: if the Kummer isomorphism over `F` sends a
power class `x` to the image of a class under `e₂(·, (e, 0))` over `F`, then the Kummer
isomorphism over `M` sends the image of `x` in `M` to the image under the character at `(e, 0)`
over `M`, both after restriction from `K`. This is
`WeierstrassCurve.explicitMap1_explicitCoeff1_twoTorsionCharacter_torsionRes` read through the
Kummer isomorphism. -/
theorem kummerIso_powerClassMap_of_kummerIso_eq [W.IsElliptic]
    {F : Type*} [Field F] [Algebra K F] [DecidableEq F]
    {M : Type*} [Field M] [Algebra K M] [Algebra F M] [IsScalarTower K F M] [DecidableEq M]
    (τ₁ : SeparableClosure K →ₐ[K] SeparableClosure F)
    (τ : SeparableClosure K →ₐ[K] SeparableClosure M) {e : F}
    (hT : (W.baseChange F).toAffine.Nonsingular e 0)
    (hψ : (W.baseChange F).toAffine.polynomialY.evalEval e 0 = 0)
    (hT' : (W.baseChange M).toAffine.Nonsingular (algebraMap F M e) 0)
    (hψ' : (W.baseChange M).toAffine.polynomialY.evalEval (algebraMap F M e) 0 = 0)
    (h2F : IsUnit ((2 : ℕ) : F)) (h2M : IsUnit ((2 : ℕ) : M))
    (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) {x : powerClassQuotient Fˣ 2}
    (hx : kummerIso F 2 h2F x = .ofAdd (explicitCoeff1 _ _
      ((W.baseChange F).twoTorsionCharacter hT hψ h2F) continuous_of_discreteTopology
      (W.torsionRes τ₁ 2 c))) :
    kummerIso M 2 h2M (powerClassMap 2 (Units.map (algebraMap F M : F →* M)) x) =
      .ofAdd (explicitCoeff1 _ _ ((W.baseChange M).twoTorsionCharacter hT' hψ' h2M)
        continuous_of_discreteTopology (W.torsionRes τ 2 c)) := by
  let τ' : SeparableClosure F →ₐ[F] SeparableClosure M := IsSepClosed.lift
  apply Multiplicative.toAdd.injective
  rw [← explicitMap1_kummerIso 2 τ' h2F, hx, toAdd_ofAdd, toAdd_ofAdd,
    W.explicitMap1_explicitCoeff1_twoTorsionCharacter_torsionRes τ₁ τ' τ hT hψ hT' hψ']

end ChangeOfField

/-! ### The map `P ↦ x(P) - e` and the Kummer map -/

section Descent

open WeierstrassCurve.Affine.Point

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) {e t : K}
  (hT : W.toAffine.Nonsingular e t) (hψ : W.toAffine.polynomialY.evalEval e t = 0)

variable {W}

omit [DecidableEq K] in
/-- The Galois group acts on `ψ₂` of the base change through the coordinates. -/
private theorem evalEval_polynomialY_galois (σ : AbsoluteGaloisGroup K)
    (x y : SeparableClosure K) :
    σ ((W⁄(SeparableClosure K)).toAffine.polynomialY.evalEval x y) =
      (W⁄(SeparableClosure K)).toAffine.polynomialY.evalEval (σ x) (σ y) := by
  simp [Affine.evalEval_polynomialY, WeierstrassCurve.baseChange, map_ofNat]

omit [DecidableEq K] in
/-- The Galois group acts on a unit `Units.mk0 a _` of `Kˢ` through `a`. -/
private theorem val_smul_mk0 (σ : AbsoluteGaloisGroup K) {a : SeparableClosure K} (ha : a ≠ 0) :
    ((σ • Units.mk0 a ha : (SeparableClosure K)ˣ) : SeparableClosure K) = σ a := by
  rw [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0]

open scoped Classical in
/-- **The Galois action on a half of a point of `E(K)`**: if `2Q` lies in `E(K)`, then the
coordinates of `σ Q` are those of `Q + S`, for the point `S = σ Q - Q`, which has `2S = O`, and `S`
is `O` or `T` exactly when `σ Q - Q` is. -/
private theorem coords_smul_eq_and_add_self_eq_zero {P : W.toAffine.Point}
    {x y : SeparableClosure K} {hQ : (W⁄(SeparableClosure K)).toAffine.Nonsingular x y}
    (h2Q : 2 • W.pointCoeffEquiv (some x y hQ) = W.basePointCoeff P) (σ : AbsoluteGaloisGroup K) :
    let S := W.pointCoeffEquiv.symm (σ • W.pointCoeffEquiv (some x y hQ) -
      W.pointCoeffEquiv (some x y hQ))
    σ x = (some x y hQ + S).xCoord ∧ σ y = (some x y hQ + S).yCoord ∧ S + S = 0 ∧
      (σ • W.pointCoeffEquiv (some x y hQ) - W.pointCoeffEquiv (some x y hQ) = 0 ∨
          σ • W.pointCoeffEquiv (some x y hQ) - W.pointCoeffEquiv (some x y hQ) =
            W.basePointCoeff (some e t hT) ↔
        S = 0 ∨ S = some (algebraMap K _ e) (algebraMap K _ t)
          ((W.toAffine.baseChange_nonsingular (Algebra.ofId K (SeparableClosure K)).injective
            e t).2 hT)) := by
  intro S
  have hmap : Affine.Point.map σ.toAlgHom (some x y hQ) = some x y hQ + S := by
    rw [← W.pointCoeffEquiv.injective.eq_iff, map_add, AddEquiv.apply_symm_apply,
      ← smul_pointCoeffEquiv, add_sub_cancel]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hmap, Affine.Point.map_some, xCoord_some, AlgEquiv.coe_toAlgHom]
  · rw [← hmap, Affine.Point.map_some, yCoord_some, AlgEquiv.coe_toAlgHom]
  · have h := smul_sub_mem_torsionCoeff h2Q σ
    rw [AddSubgroup.torsionBy.nsmul_iff, two_nsmul] at h
    rw [← W.pointCoeffEquiv.injective.eq_iff, map_add, AddEquiv.apply_symm_apply, h,
      _root_.map_zero]
  · rw [← W.pointCoeffEquiv.symm.injective.eq_iff, ← W.pointCoeffEquiv.symm.injective.eq_iff,
      _root_.map_zero, basePointCoeff_some, AddEquiv.symm_apply_apply]

open scoped Classical in
/-- **A Kummer root of `x(P) - e` for an affine halving point**: the case of
`exists_sq_eq_and_smul_eq` where `Q = (x, y)` is an affine point with `ψ₂(Q) ≠ 0`. -/
private theorem exists_sq_eq_and_smul_eq_some {xP yP : K} (hP : W.toAffine.Nonsingular xP yP)
    {x y : SeparableClosure K} (hQ' : (W⁄(SeparableClosure K)).toAffine.Nonsingular x y)
    (hP' : (W⁄(SeparableClosure K)).toAffine.Nonsingular
      (algebraMap K (SeparableClosure K) xP) (algebraMap K (SeparableClosure K) yP))
    (hQ : 2 • W.pointCoeffEquiv (some x y hQ') = W.basePointCoeff (some xP yP hP))
    (hQQ : some x y hQ' + some x y hQ' = some (algebraMap K (SeparableClosure K) xP)
      (algebraMap K (SeparableClosure K) yP) hP')
    (hy : (W⁄(SeparableClosure K)).toAffine.polynomialY.evalEval x y ≠ 0) :
    ∃ α : (SeparableClosure K)ˣ,
      α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom
        (W.twoDescentUnit hT hψ (some xP yP hP)) ∧
      ∀ σ : AbsoluteGaloisGroup K, σ • α =
        (if σ • W.pointCoeffEquiv (some x y hQ') - W.pointCoeffEquiv (some x y hQ') = 0 ∨
          σ • W.pointCoeffEquiv (some x y hQ') - W.pointCoeffEquiv (some x y hQ') =
            W.basePointCoeff (some e t hT) then 1 else -1) * α := by
  set ι := algebraMap K (SeparableClosure K)
  have hT' : (W⁄(SeparableClosure K)).toAffine.Nonsingular (ι e) (ι t) :=
    (W.toAffine.baseChange_nonsingular (Algebra.ofId K (SeparableClosure K)).injective e t).2 hT
  have hψ' : (W⁄(SeparableClosure K)).toAffine.polynomialY.evalEval (ι e) (ι t) = 0 := by
    rw [baseChange, Affine.map_polynomialY, Polynomial.map_mapRingHom_evalEval, hψ,
      _root_.map_zero]
  have hc' : (W⁄(SeparableClosure K)).toAffine.polynomialX.evalEval (ι e) (ι t) =
      ι (W.toAffine.polynomialX.evalEval e t) := by
    rw [baseChange, Affine.map_polynomialX, Polynomial.map_mapRingHom_evalEval]
  -- `x(2Q) - e` is the square of `((x - e)² + W_X(e, t)) / ψ₂(Q)`
  have hdup := Affine.Point.xCoord_add_self_sub_mul_sq hT'.1 hψ' hQ' hy
  rw [hQQ, xCoord_some, hc'] at hdup
  -- the action of `σ` on the coordinates of `Q`
  have hσ (σ : AbsoluteGaloisGroup K) := coords_smul_eq_and_add_self_eq_zero hT hQ σ
  by_cases hxe : xP = e
  · -- `P = T`: the root is `x(Q) - e`
    subst hxe
    have hx2 : (x - ι xP) ^ 2 + ι (W.toAffine.polynomialX.evalEval xP t) = 0 :=
      pow_eq_zero_iff (n := 2) two_ne_zero |>.1 <| by rw [← hdup, sub_self, zero_mul]
    have hxne := Affine.X_ne_of_evalEval_polynomialY_ne_zero hT'.1 hψ' hQ'.1 hy
    refine ⟨Units.mk0 (x - ι xP) (sub_ne_zero.2 hxne), Units.ext ?_, fun σ ↦ Units.ext ?_⟩
    · simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.coe_map, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_ofClass, coe_twoDescentUnit_some_of_eq _ _ _ _ rfl, map_neg]
      linear_combination hx2
    · obtain ⟨hσx, -, hS, hiff⟩ := hσ σ
      simp only [Units.val_mul, val_smul_mk0, Units.val_mk0]
      rw [map_sub, AlgEquiv.commutes, hσx,
        Affine.Point.xCoord_add_sub hT' hψ' hQ' hy (by rwa [hc']) hS]
      simp only [hiff, apply_ite Units.val, Units.val_one, Units.val_neg, ι]
  · -- `P ≠ T`: the root is `((x - e)² + W_X(e, t)) / ψ₂(Q)`
    set ψ := (W⁄(SeparableClosure K)).toAffine.polynomialY.evalEval x y
    set c := W.toAffine.polynomialX.evalEval e t
    have hα2 : (((x - ι e) ^ 2 + ι c) / ψ) ^ 2 = ι xP - ι e := by
      rw [div_pow, div_eq_iff (pow_ne_zero 2 hy), hdup]
    have hα0 : ((x - ι e) ^ 2 + ι c) / ψ ≠ 0 := fun h0 ↦ hxe <| ι.injective <| by
      rwa [h0, zero_pow two_ne_zero, eq_comm, sub_eq_zero] at hα2
    refine ⟨Units.mk0 _ hα0, Units.ext ?_, fun σ ↦ Units.ext ?_⟩
    · simp [hα2, coe_twoDescentUnit_some_of_ne _ _ _ _ hxe]
    · obtain ⟨hσx, hσy, hS, hiff⟩ := hσ σ
      have hroot :=
        Affine.Point.sq_xCoord_add_sub_add_evalEval_polynomialX_div hT' hψ' hQ' hy hS
      rw [hc'] at hroot
      simp only [Units.val_mul, val_smul_mk0, Units.val_mk0, map_div₀, map_add, map_pow, map_sub]
      rw [AlgEquiv.commutes, AlgEquiv.commutes, evalEval_polynomialY_galois, hσx, hσy, hroot]
      simp only [hiff, apply_ite Units.val, Units.val_one, Units.val_neg, ι, ψ]

open scoped Classical in
/-- **A Kummer root of `x(P) - e`**: if `2Q = P ≠ O`, the unit `x(P) - e` (or `c_T` at `P = T`)
has a square root `α` in `Kˢ` on which `σ` acts by `1` when `σ Q - Q ∈ {O, T}` and by `-1`
otherwise. -/
private theorem exists_sq_eq_and_smul_eq {xP yP : K} (hP : W.toAffine.Nonsingular xP yP)
    {Q : W.PointCoeff} (hQ : 2 • Q = W.basePointCoeff (some xP yP hP)) :
    ∃ α : (SeparableClosure K)ˣ,
      α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom
        (W.twoDescentUnit hT hψ (some xP yP hP)) ∧
      ∀ σ : AbsoluteGaloisGroup K, σ • α =
        (if σ • Q - Q = 0 ∨ σ • Q - Q = W.basePointCoeff (some e t hT) then 1 else -1) * α := by
  obtain ⟨Q, rfl⟩ := W.pointCoeffEquiv.surjective Q
  set ι := algebraMap K (SeparableClosure K)
  have hP' : (W⁄(SeparableClosure K)).toAffine.Nonsingular (ι xP) (ι yP) :=
    (W.toAffine.baseChange_nonsingular (Algebra.ofId K (SeparableClosure K)).injective xP yP).2 hP
  have hQQ : Q + Q = some (ι xP) (ι yP) hP' := W.pointCoeffEquiv.injective <| by
    rw [map_add, ← two_nsmul, hQ, basePointCoeff_some]
  -- `Q` is an affine point with `ψ₂(Q) ≠ 0`, since `2Q ≠ O`
  rcases Q with _ | ⟨x, y, hQ'⟩
  · rw [← zero_def, add_zero] at hQQ
    exact absurd hQQ.symm (some_ne_zero _)
  have hy : (W⁄(SeparableClosure K)).toAffine.polynomialY.evalEval x y ≠ 0 := fun hy ↦
    some_ne_zero hP' <| hQQ ▸ (Affine.Point.some_add_self_eq_zero_iff hQ').2 hy
  exact exists_sq_eq_and_smul_eq_some hT hψ hP hQ' hP' hQ hQQ hy

end Descent

end WeierstrassCurve
