/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Adapted from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 5a01f5fe3621,
-- module TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.TwoDescent), Apache-2.0:
-- without the Weil-pairing comparison; restriction compatibility proved directly
-- (Lane R7, fork issue #83).
import ZInQKernel.Contrib.TauCeti.Algebra.Algebra.NatCast
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Descent
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Restriction
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.IsSepClosed
import ZInQKernel.Contrib.TauCeti.FieldTheory.GaloisCohomology.Kummer
import ZInQKernel.Contrib.TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic

/-!
# The Kummer map of multiplication by two is `x - e` (without the Weil pairing)

Lane R7 of fork issue #83. This file is Tau Ceti's
`ZInQKernel/Contrib/TauCeti/AlgebraicGeometry/EllipticCurve/GaloisCohomology/TwoDescent.lean`
(vendored from Tau Ceti, commit 5a01f5fe3621, Apache-2.0), adapted so that its import closure avoids
the Weil-pairing development (`GaloisCohomology.WeilPairing`, `Isogeny.MulByInt.WeilPairing.*` and
the function-field divisor files below them), whose `WeierstrassCurve.Affine.divisorSum` collides
with another vendored definition of the same name elsewhere in the repository. The changes:

* the declarations live in the namespace `ZInQ.Manuscript.PoleRC.SelMTauCeti` instead of
  `WeierstrassCurve`;
* the comparison `twoTorsionCharacter_eq_weilPairing` with the Weil pairing is omitted (nothing here
  uses it: the character is defined through the subgroup `{O, T}`);
* the compatibility of the character with restriction to a field extension, which Tau Ceti derives
  from the Weil pairing, is proved directly (`explicitMap1_explicitCoeff1_twoTorsionCharacter`).

Let `W` be an elliptic curve over a field `K` in which `2` is invertible, and let `T = (e, t)` be a
point of `W(K)` of order two. The character `E(Kˢ)[2] → μ₂` which is trivial exactly on `{O, T}`
carries the Kummer class of `P ∈ E(K)` in `H¹(G_K, E[2])` to the Kummer class in `H¹(G_K, μ₂)` of
`x(P) - e`, with `O ↦ 1` and `T ↦ c_T = -W_X(e, t)` (Silverman X.1.4).

## Main definitions

* `twoTorsionCoeff`: the point `T`, as an element of `E(Kˢ)[2]`.
* `twoTorsionCharacter`: the character `E(Kˢ)[2] → μ₂`, trivial exactly on `{O, T}`.
* `twoDescentUnit`: the map `E(K) → Kˣ`, `P ↦ x(P) - e`, with `O ↦ 1` and `T ↦ c_T`.

## Main results

* `coe_toMul_twoTorsionCharacter`: the character is `1` on `{O, T}` and `-1` off it.
* `explicitCoeff1_twoTorsionCharacter_kummerMap`: the image of the Kummer class of `P` under the
  character is the Kummer class of `x(P) - e`.
* `explicitMap1_explicitCoeff1_twoTorsionCharacter`: the character commutes with restriction.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.1.4.
-/

noncomputable section

open TauCeti TauCeti.ContCohomology

namespace ZInQ.Manuscript.PoleRC.SelMTauCeti

open WeierstrassCurve

/-! ### The character `E(Kˢ)[2] → μ₂` attached to `T` -/

section Character

open WeierstrassCurve.Affine.Point

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) {e t : K}
  (hT : W.toAffine.Nonsingular e t) (hψ : W.toAffine.polynomialY.evalEval e t = 0)

/-- **The point `T` of order two, as an element of `E(Kˢ)[2]`**: its image under
`WeierstrassCurve.baseTorsionCoeff`. -/
def twoTorsionCoeff : W.TorsionCoeff 2 :=
  W.baseTorsionCoeff 2 ⟨some e t hT, by
    rw [AddSubgroup.torsionBy.nsmul_iff, two_nsmul,
      (Affine.Point.some_add_self_eq_zero_iff hT).2 hψ]⟩

/-- `twoTorsionCoeff` is the image of `T` in `E(Kˢ)`. -/
@[simp]
theorem coe_twoTorsionCoeff :
    (twoTorsionCoeff W hT hψ : W.PointCoeff) = W.basePointCoeff (some e t hT) :=
  W.coe_baseTorsionCoeff _

/-- `T` is a nonzero element of `E(Kˢ)[2]`. -/
theorem twoTorsionCoeff_ne_zero : twoTorsionCoeff W hT hψ ≠ 0 := fun h ↦
  some_ne_zero hT <| W.basePointCoeff_injective <| by
    rw [← coe_twoTorsionCoeff W hT hψ, h, _root_.map_zero, ZeroMemClass.coe_zero]

/-- `T` has order two in `E(Kˢ)[2]`. -/
theorem addOrderOf_twoTorsionCoeff : addOrderOf (twoTorsionCoeff W hT hψ) = 2 :=
  addOrderOf_eq_prime (Subtype.ext <| by
    rw [AddSubgroup.coe_nsmul, coe_twoTorsionCoeff, ← map_nsmul, two_nsmul,
      (Affine.Point.some_add_self_eq_zero_iff hT).2 hψ, _root_.map_zero, ZeroMemClass.coe_zero])
    (twoTorsionCoeff_ne_zero W hT hψ)

/-- The multiples of `T` in `E(Kˢ)[2]` are `O` and `T`. -/
theorem mem_zmultiples_twoTorsionCoeff_iff {S : W.TorsionCoeff 2} :
    S ∈ AddSubgroup.zmultiples (twoTorsionCoeff W hT hψ) ↔
      (S : W.PointCoeff) = 0 ∨ (S : W.PointCoeff) = W.basePointCoeff (some e t hT) := by
  have e₁ : (S : W.PointCoeff) = 0 ↔ S = 0 := ZeroMemClass.coe_eq_zero
  have e₂ : (S : W.PointCoeff) = W.basePointCoeff (some e t hT) ↔ S = twoTorsionCoeff W hT hψ := by
    rw [← coe_twoTorsionCoeff W hT hψ, Subtype.coe_inj]
  rw [e₁, e₂]
  refine ⟨?_, ?_⟩
  · rintro ⟨n, rfl⟩
    dsimp only
    rw [← mod_addOrderOf_zsmul, addOrderOf_twoTorsionCoeff]
    simp only [Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · exact Or.inl (by rw [h, zero_zsmul])
    · exact Or.inr (by rw [h, one_zsmul])
  · rintro (rfl | rfl)
    · exact zero_mem _
    · exact AddSubgroup.mem_zmultiples _

/-- `{O, T}` has index two in `E(Kˢ)[2]`. -/
theorem index_zmultiples_twoTorsionCoeff [W.IsElliptic] (h2 : IsUnit ((2 : ℕ) : K)) :
    (AddSubgroup.zmultiples (twoTorsionCoeff W hT hψ)).index = 2 := by
  have h := (AddSubgroup.zmultiples (twoTorsionCoeff W hT hψ)).card_mul_index
  rw [Nat.card_zmultiples, addOrderOf_twoTorsionCoeff, natCard_torsionCoeff W h2] at h
  omega

/-- **The character `E(Kˢ)[2] → μ₂` attached to a point `T` of order two**, trivial exactly on
`{O, T}`: a homomorphism of discrete `G_K`-modules, for `2` invertible in `K`, since `{O, T}` has
index two in `E(Kˢ)[2]` and is stable under `G_K`. It is the Weil pairing `e₂(·, T)`
(Tau Ceti's `WeierstrassCurve.twoTorsionCharacter_eq_weilPairing`, not used here). -/
def twoTorsionCharacter [W.IsElliptic] (h2 : IsUnit ((2 : ℕ) : K)) :
    W.TorsionCoeff 2 →+[AbsoluteGaloisGroup K] KummerCoeff K 2 where
  toFun S := if S ∈ AddSubgroup.zmultiples (twoTorsionCoeff W hT hψ) then 0 else mu2NegOne
  map_zero' := ite_eq_left (zero_mem _)
  map_add' S₁ S₂ := by
    have hadd := AddSubgroup.add_mem_iff_of_index_two
      (index_zmultiples_twoTorsionCoeff W hT hψ h2) (a := S₁) (b := S₂)
    by_cases h₁ : S₁ ∈ AddSubgroup.zmultiples (twoTorsionCoeff W hT hψ) <;>
      by_cases h₂ : S₂ ∈ AddSubgroup.zmultiples (twoTorsionCoeff W hT hψ)
    · rw [ite_eq_left (hadd.2 (iff_of_true h₁ h₂)), ite_eq_left h₁, ite_eq_left h₂, add_zero]
    · rw [ite_eq_right fun h ↦ h₂ (hadd.1 h |>.1 h₁), ite_eq_left h₁, ite_eq_right h₂, zero_add]
    · rw [ite_eq_right fun h ↦ h₁ (hadd.1 h |>.2 h₂), ite_eq_right h₁, ite_eq_left h₂, add_zero]
    · rw [ite_eq_left (hadd.2 (iff_of_false h₁ h₂)), ite_eq_right h₁, ite_eq_right h₂]
      exact Additive.toMul.injective <| Subtype.ext <| Units.ext <| by simp
  map_smul' σ S := by
    have hσ : σ • S ∈ AddSubgroup.zmultiples (twoTorsionCoeff W hT hψ) ↔
        S ∈ AddSubgroup.zmultiples (twoTorsionCoeff W hT hψ) := by
      rw [mem_zmultiples_twoTorsionCoeff_iff, mem_zmultiples_twoTorsionCoeff_iff,
        coe_smul_torsionCoeff, smul_eq_zero_iff_eq, smul_eq_iff_eq_inv_smul, smul_basePointCoeff]
    simp only [hσ, MonoidHom.id_apply]
    exact (mu2_smul_eq_self K σ _).symm

/-- The definition of `twoTorsionCharacter`, through the subgroup `{O, T}` of `E(Kˢ)[2]`. -/
private theorem twoTorsionCharacter_apply [W.IsElliptic] (h2 : IsUnit ((2 : ℕ) : K))
    (S : W.TorsionCoeff 2) :
    twoTorsionCharacter W hT hψ h2 S =
      if S ∈ AddSubgroup.zmultiples (twoTorsionCoeff W hT hψ) then 0 else mu2NegOne :=
  (rfl)

open scoped Classical in
/-- **The values of `twoTorsionCharacter`**: `1` on `O` and `T`, and `-1` on the other two points
of `E(Kˢ)[2]`. -/
theorem coe_toMul_twoTorsionCharacter [W.IsElliptic] (h2 : IsUnit ((2 : ℕ) : K))
    (S : W.TorsionCoeff 2) :
    (((twoTorsionCharacter W hT hψ h2 S).toMul : rootsOfUnity 2 (SeparableClosure K)) :
        (SeparableClosure K)ˣ) =
      if (S : W.PointCoeff) = 0 ∨ (S : W.PointCoeff) = W.basePointCoeff (some e t hT) then 1
      else -1 := by
  rw [twoTorsionCharacter_apply]
  by_cases h : S ∈ AddSubgroup.zmultiples (twoTorsionCoeff W hT hψ)
  · rw [ite_eq_left h, ite_eq_left ((mem_zmultiples_twoTorsionCoeff_iff W hT hψ).1 h), toMul_zero,
      OneMemClass.coe_one]
  · rw [ite_eq_right h, ite_eq_right (mt (mem_zmultiples_twoTorsionCoeff_iff W hT hψ).2 h),
      toMul_mu2NegOne]

/-- **`twoTorsionCharacter` is trivial exactly on `{O, T}`.** -/
theorem twoTorsionCharacter_eq_zero_iff [W.IsElliptic] (h2 : IsUnit ((2 : ℕ) : K))
    {S : W.TorsionCoeff 2} :
    twoTorsionCharacter W hT hψ h2 S = 0 ↔
      (S : W.PointCoeff) = 0 ∨ (S : W.PointCoeff) = W.basePointCoeff (some e t hT) := by
  let : Invertible (2 : K) := (by simpa using h2 : IsUnit (2 : K)).invertible
  rw [twoTorsionCharacter_apply, ← mem_zmultiples_twoTorsionCoeff_iff W hT hψ]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false mu2NegOne_ne_zero h

end Character

/-! ### The map `P ↦ x(P) - e` and the Kummer map -/

section Descent

open WeierstrassCurve.Affine.Point

variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) {e t : K}
  (hT : W.toAffine.Nonsingular e t) (hψ : W.toAffine.polynomialY.evalEval e t = 0)

/-- **The `2`-descent map attached to a point `T = (e, t)` of order two**: `P ↦ x(P) - e`, as a
unit of `K`, with `O ↦ 1` and `T ↦ c_T = -W_X(e, t)`, the value at `T` of the derivative of the
Weierstrass equation in `x`. Its square class is the image of the Kummer class of `P` under the
character `E[2] → μ₂` attached to `T`
(`explicitCoeff1_twoTorsionCharacter_kummerMap`). -/
def twoDescentUnit : W.toAffine.Point → Kˣ
  | .zero => 1
  | .some x _ _ =>
    if hx : x = e then
      Units.mk0 (-W.toAffine.polynomialX.evalEval e t)
        (neg_ne_zero.2 (hT.2.resolve_right (not_not.2 hψ)))
    else Units.mk0 (x - e) (sub_ne_zero.2 hx)

/-- The `2`-descent map sends `O` to `1`. -/
@[simp]
theorem twoDescentUnit_zero : twoDescentUnit W hT hψ 0 = 1 :=
  (rfl)

/-- Away from `T`, the `2`-descent map is `x - e`. -/
theorem coe_twoDescentUnit_some_of_ne {x y : K} (h : W.toAffine.Nonsingular x y) (hx : x ≠ e) :
    (twoDescentUnit W hT hψ (some x y h) : K) = x - e := by
  rw [twoDescentUnit, dite_eq_right hx, Units.val_mk0]

/-- At `T`, the `2`-descent map is `c_T = -W_X(e, t)`. -/
theorem coe_twoDescentUnit_some_of_eq {x y : K} (h : W.toAffine.Nonsingular x y) (hx : x = e) :
    (twoDescentUnit W hT hψ (some x y h) : K) = -W.toAffine.polynomialX.evalEval e t := by
  rw [twoDescentUnit, dite_eq_left hx, Units.val_mk0]

variable {W}

omit [DecidableEq K] in
/-- The Galois group acts on `ψ₂` of the base change through the coordinates. -/
private theorem evalEval_polynomialY_galois (σ : AbsoluteGaloisGroup K)
    (x y : SeparableClosure K) :
    σ ((W⁄(SeparableClosure K)).toAffine.polynomialY.evalEval x y) =
      (W⁄(SeparableClosure K)).toAffine.polynomialY.evalEval (σ x) (σ y) := by
  simp [Affine.evalEval_polynomialY, WeierstrassCurve.baseChange, map_ofNat]

omit [DecidableEq K] in
-- Without the Weil-pairing files in scope, finding the action of `G_K` on `(Kˢ)ˣ` takes longer.
set_option synthInstance.maxHeartbeats 400000 in
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

set_option synthInstance.maxHeartbeats 400000 in
open scoped Classical in
/-- **A Kummer root of `x(P) - e`**: if `2Q = P ≠ O`, the unit `x(P) - e` (or `c_T` at `P = T`)
has a square root `α` in `Kˢ` on which `σ` acts by `1` when `σ Q - Q ∈ {O, T}` and by `-1`
otherwise. -/
private theorem exists_sq_eq_and_smul_eq {xP yP : K} (hP : W.toAffine.Nonsingular xP yP)
    {Q : W.PointCoeff} (hQ : 2 • Q = W.basePointCoeff (some xP yP hP)) :
    ∃ α : (SeparableClosure K)ˣ,
      α ^ 2 = Units.map (algebraMap K (SeparableClosure K)).toMonoidHom
        (twoDescentUnit W hT hψ (some xP yP hP)) ∧
      ∀ σ : AbsoluteGaloisGroup K, σ • α =
        (if σ • Q - Q = 0 ∨ σ • Q - Q = W.basePointCoeff (some e t hT) then 1 else -1) * α := by
  obtain ⟨Q, rfl⟩ := W.pointCoeffEquiv.surjective Q
  set ι := algebraMap K (SeparableClosure K)
  have hT' : (W⁄(SeparableClosure K)).toAffine.Nonsingular (ι e) (ι t) :=
    (W.toAffine.baseChange_nonsingular (Algebra.ofId K (SeparableClosure K)).injective e t).2 hT
  have hψ' : (W⁄(SeparableClosure K)).toAffine.polynomialY.evalEval (ι e) (ι t) = 0 := by
    rw [WeierstrassCurve.baseChange, Affine.map_polynomialY, Polynomial.map_mapRingHom_evalEval, hψ,
      _root_.map_zero]
  have hc' : (W⁄(SeparableClosure K)).toAffine.polynomialX.evalEval (ι e) (ι t) =
      ι (W.toAffine.polynomialX.evalEval e t) := by
    rw [WeierstrassCurve.baseChange, Affine.map_polynomialX, Polynomial.map_mapRingHom_evalEval]
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

/-- **The Kummer map of `[2]`, read through a point of order two, is `x - e`** (Silverman X.1.4).
Let `T = (e, t)` be a point of `W(K)` of order two, with `2` invertible in `K`. The character
`E(Kˢ)[2] → μ₂` trivial exactly on `{O, T}` carries the Kummer class of `P ∈ E(K)` in
`H¹(G_K, E[2])` to the Kummer class in `H¹(G_K, μ₂)` of `x(P) - e`, where `O ↦ 1` and
`T ↦ c_T = -W_X(e, t)`. -/
theorem explicitCoeff1_twoTorsionCharacter_kummerMap [W.IsElliptic] (h2 : IsUnit ((2 : ℕ) : K))
    (P : W.toAffine.Point) :
    explicitCoeff1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2) (twoTorsionCharacter W hT hψ h2)
        continuous_of_discreteTopology (W.kummerMap 2 h2 P) =
      Multiplicative.toAdd (TauCeti.kummerMap K 2 h2 (twoDescentUnit W hT hψ P)) := by
  rcases P with _ | ⟨xP, yP, hP⟩
  · rw [← zero_def, _root_.map_zero, _root_.map_zero, twoDescentUnit_zero, _root_.map_one,
      toAdd_one]
  obtain ⟨Q, hQ⟩ := (W.kummerShortExact 2 h2).proj_surjective (W.basePointCoeff (some xP yP hP))
  rw [WeierstrassCurve.kummerShortExact_proj, nsmulAddMonoidHom_apply] at hQ
  obtain ⟨α, hα, hσα⟩ := exists_sq_eq_and_smul_eq hT hψ hP hQ
  rw [WeierstrassCurve.kummerMap_eq_H1pi h2 hQ, QuotientAddGroup.mk'_apply, explicitCoeff1_mk,
    TauCeti.kummerMap_eq_kummerCocycleClass h2 hα, TauCeti.kummerCocycleClass_def,
    QuotientAddGroup.mk'_apply]
  -- the two cocycles agree: `σ α / α` is the sign of `σ Q - Q`
  have key (σ : AbsoluteGaloisGroup K) :
      twoTorsionCharacter W hT hψ h2 (WeierstrassCurve.kummerCocycle hQ σ) =
        TauCeti.kummerCocycle hα σ :=
    Additive.toMul.injective <| Subtype.ext <| by
      rw [coe_toMul_twoTorsionCharacter, WeierstrassCurve.coe_kummerCocycle,
        TauCeti.toMul_kummerCocycle, hσα σ, mul_inv_cancel_right]
  exact congrArg _ <| Subtype.ext <| funext fun σ ↦
    (cocyclesMap1_apply _ _ _ _ _ _ _ _ _ σ).trans (key σ)

end Descent


/-! ### Compatibility with restriction to a field extension -/

section Restriction

variable {K : Type*} [Field K] [DecidableEq K] {L : Type*} [Field L] [Algebra K L] [DecidableEq L]
  (W : WeierstrassCurve K) (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

omit [DecidableEq K] [DecidableEq L] in
/-- The map `E(Kˢ) → E(Lˢ)` along `τ` is injective. -/
theorem pointCoeffBaseChange_injective : Function.Injective (W.pointCoeffBaseChange τ) := by
  classical
  intro P Q h
  simp only [pointCoeffBaseChange, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    EmbeddingLike.apply_eq_iff_eq] at h
  exact W.pointCoeffEquiv.symm.injective (Affine.Point.map_injective τ h)

variable {W}

/-- **The character commutes with base change**: for `T' = (e', t')` the image of `T = (e, t)`
in `W(L)`, the character of `T'` on the base change of `S ∈ E(Kˢ)[2]` is the base change of the
character of `T` on `S`. -/
theorem kummerCoeffBaseChange_twoTorsionCharacter [W.IsElliptic] {e t : K}
    (hT : W.toAffine.Nonsingular e t) (hψ : W.toAffine.polynomialY.evalEval e t = 0)
    (h2 : IsUnit ((2 : ℕ) : K)) {e' t' : L} (hT' : (W⁄L).toAffine.Nonsingular e' t')
    (hψ' : (W⁄L).toAffine.polynomialY.evalEval e' t' = 0) (h2' : IsUnit ((2 : ℕ) : L))
    (he : e' = algebraMap K L e) (ht : t' = algebraMap K L t) (S : W.TorsionCoeff 2) :
    kummerCoeffBaseChange 2 τ (twoTorsionCharacter W hT hψ h2 S) =
      twoTorsionCharacter (W⁄L) hT' hψ' h2' (W.torsionCoeffBaseChange τ 2 S) := by
  classical
  subst he ht
  have hpt : W.toAffine.pointMap L (Affine.Point.some e t hT) =
      Affine.Point.some (algebraMap K L e) (algebraMap K L t) hT' := by
    rw [Affine.pointMap_some]
  have key : ((W.torsionCoeffBaseChange τ 2 S : (W⁄L).PointCoeff) = 0 ∨
        (W.torsionCoeffBaseChange τ 2 S : (W⁄L).PointCoeff) =
          (W⁄L).basePointCoeff (Affine.Point.some (algebraMap K L e) (algebraMap K L t) hT')) ↔
      ((S : W.PointCoeff) = 0 ∨
        (S : W.PointCoeff) = W.basePointCoeff (Affine.Point.some e t hT)) := by
    rw [coe_torsionCoeffBaseChange, ← hpt, ← pointCoeffBaseChange_basePointCoeff,
      (pointCoeffBaseChange_injective W τ).eq_iff, ← map_zero (W.pointCoeffBaseChange τ),
      (pointCoeffBaseChange_injective W τ).eq_iff]
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [toMul_kummerCoeffBaseChange, coe_toMul_twoTorsionCharacter, coe_toMul_twoTorsionCharacter]
  split_ifs with h₁ h₂ h₂
  · exact map_one _
  · exact absurd (key.mpr h₁) h₂
  · exact absurd (key.mp h₂) h₁
  · exact Units.ext (by simp)

/-- **Restriction commutes with the character** (the counterpart of Tau Ceti's
`WeierstrassCurve.explicitMap1_explicitCoeff1_weilPairingCoeff`, proved without the Weil pairing):
restricting to `G_L` and then applying the character of `T'` is applying the character of `T` and
then restricting the roots of unity along `τ`. -/
theorem explicitMap1_explicitCoeff1_twoTorsionCharacter [W.IsElliptic] {e t : K}
    (hT : W.toAffine.Nonsingular e t) (hψ : W.toAffine.polynomialY.evalEval e t = 0)
    (h2 : IsUnit ((2 : ℕ) : K)) {e' t' : L} (hT' : (W⁄L).toAffine.Nonsingular e' t')
    (hψ' : (W⁄L).toAffine.polynomialY.evalEval e' t' = 0) (h2' : IsUnit ((2 : ℕ) : L))
    (he : e' = algebraMap K L e) (ht : t' = algebraMap K L t)
    (c : H1 (AbsoluteGaloisGroup K) (W.TorsionCoeff 2)) :
    explicitMap1 _ _ _ _ (absoluteGaloisGroupMap τ) (kummerCoeffBaseChange 2 τ)
        continuous_of_discreteTopology (kummerCoeffBaseChange_smul 2 τ)
        (explicitCoeff1 _ _ (twoTorsionCharacter W hT hψ h2) continuous_of_discreteTopology c) =
      explicitCoeff1 _ _ (twoTorsionCharacter (W⁄L) hT' hψ' h2') continuous_of_discreteTopology
        (W.torsionRes τ 2 c) := by
  rw [explicitCoeff1_eq_explicitMap1, explicitCoeff1_eq_explicitMap1, torsionRes_eq_explicitMap1]
  refine explicitMap1_explicitMap1_of_comp_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (by ext; rfl) (AddMonoidHom.ext fun S ↦ ?_) c
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, DistribMulActionHom.coe_fn_coe]
  exact kummerCoeffBaseChange_twoTorsionCharacter τ hT hψ h2 hT' hψ' h2' he ht S

end Restriction

end ZInQ.Manuscript.PoleRC.SelMTauCeti
