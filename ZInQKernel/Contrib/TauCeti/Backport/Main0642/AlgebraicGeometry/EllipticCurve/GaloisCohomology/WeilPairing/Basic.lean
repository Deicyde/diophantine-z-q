/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 0642eae29e0a, module
-- TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing.Basic), Apache-2.0: declarations of that module absent from its commit-5a01f5fe version, which
-- is vendored as `ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing` (task selmer-2infty).
-- Modified for the Z-in-Q kernel: declarations already in the vendored module removed; imports rewritten.
module

public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.WeilPairing
public import ZInQKernel.Contrib.TauCeti.Algebra.Algebra.NatCast
public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Restriction
public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.BaseChange
public import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.RootsOfUnity
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.FieldTheory.GaloisCohomology.Kummer
public import ZInQKernel.Contrib.TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.AlgebraicGeometry.EllipticCurve.Affine.Point.TwoTorsion
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Coefficients
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.FieldTheory.Galois.AbsoluteGaloisGroup.Norm
public import ZInQKernel.Contrib.TauCeti.Backport.Main0642.FieldTheory.GaloisCohomology.Units.CoeffMap

/-!
# The Weil pairing on the Galois coefficient modules of an elliptic curve

Let `W` be an elliptic curve over a field `K` and `m` a natural number invertible in `K`. The Weil
pairing `e_m` of `W` over the separable closure `Kˢ` is a pairing on the coefficient module
`E(Kˢ)[m]` (`WeierstrassCurve.TorsionCoeff`) with values in the roots of unity `μ_m`
(`TauCeti.KummerCoeff`), and it is `G_K`-equivariant. So a `K`-rational point `T` of order
dividing `m` gives a map of discrete `G_K`-modules

```text
W.weilPairingCoeff m hm T : E(Kˢ)[m] → μ_m,    P ↦ e_m(P, T),
```

and hence a map `H¹(G_K, E[m]) → H¹(G_K, μ_m)` into the group which Kummer theory identifies with
`Kˣ ⧸ (Kˣ)ᵐ` (`TauCeti.kummerIso`). These maps are natural in the field: restriction along a field
extension `L / K` commutes with them, the roots of unity being restricted along the same embedding
of separable closures (`WeierstrassCurve.explicitMap1_explicitCoeff1_weilPairingCoeff`).

When `E[m] ⊆ E(K)`, that is when `G_K` fixes every point of `E(Kˢ)[m]`, these maps together
detect every class: a class of `H¹(G_K, E[m])` which dies in `H¹(G_K, μ_m)` under every
`weilPairingCoeff T` is zero (`WeierstrassCurve.explicitCoeff1_weilPairingCoeff_injective`).
Indeed `G_K` then acts trivially on `μ_m` as well, so a class dying in `H¹(G_K, μ_m)` is a cocycle
killed by `e_m(·, T)`, and the Weil pairing is nondegenerate. This is how the Galois cohomology of
`E[m]` over a field containing `E[m]` is reduced to Kummer theory, the step on which the weak
Mordell–Weil theorem and the finiteness of the `m`-Selmer group rest: over a number field the
classes unramified outside a finite set `S` of places are then controlled by the finite group
`K(S, m)` (Silverman VIII.1.5, VIII.1.6 and X.4.2).

## Main definitions

* `WeierstrassCurve.torsionCoeffWeilPairing`: the Weil pairing `E(Kˢ)[m] × E(Kˢ)[m] → μ_m`.
* `WeierstrassCurve.weilPairingCoeff`: for `T ∈ E(K)[m]`, the equivariant map
  `E(Kˢ)[m] → μ_m`, `P ↦ e_m(P, T)`.

## Main results

* `WeierstrassCurve.torsionCoeffWeilPairing_smul`: the Weil pairing is `G_K`-equivariant.
* `WeierstrassCurve.torsionCoeffWeilPairing_torsionCoeffBaseChange`: the Weil pairing commutes with
  the maps on torsion and on roots of unity induced by an embedding `Kˢ → Lˢ` of separable closures.
* `WeierstrassCurve.neg_torsionCoeffWeilPairing`: interchanging the arguments negates the pairing.
* `WeierstrassCurve.torsionCoeffWeilPairing_nondegenerate`: the Weil pairing is nondegenerate.
* `WeierstrassCurve.torsionCoeffWeilPairing_two_eq_mu2NegOne`: the Weil pairing of two distinct
  points of order two is the nontrivial element of `μ₂`.
* `WeierstrassCurve.torsionCoeffWeilPairing_sum_ite`: the Weil pairing of a sum of points of order
  two with a nonzero point of order two.
* `WeierstrassCurve.explicitMap1_explicitCoeff1_weilPairingCoeff`: restriction to a field
  extension commutes with the maps `H¹(G, E[m]) → H¹(G, μ_m)`.
* `WeierstrassCurve.explicitCoeff1_weilPairingCoeff_injective`: if `G_K` fixes `E(Kˢ)[m]`, the
  maps `H¹(G_K, E[m]) → H¹(G_K, μ_m)` attached to the points of `E(K)[m]` are jointly injective.
* `WeierstrassCurve.finite_of_forall_finite_image_explicitCoeff1_weilPairingCoeff`: if `G_K` fixes
  `E(Kˢ)[m]`, a set of classes of `H¹(G_K, E[m])` with finite images in `H¹(G_K, μ_m)` is finite.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.8.1, VIII.1, X.1 and X.4.
-/

public section

noncomputable section

namespace WeierstrassCurve

open TauCeti TauCeti.ContCohomology

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] (m : ℕ)
  (hm : IsUnit (m : K))

/-! ### The Weil pairing on `E(Kˢ)[m]` -/

/-- Interchanging the arguments negates the Weil pairing on the coefficient module. -/
theorem neg_torsionCoeffWeilPairing (P Q : W.TorsionCoeff m) :
    -W.torsionCoeffWeilPairing m hm P Q = W.torsionCoeffWeilPairing m hm Q P := by
  classical
  have := hm.neZero_natCast
  simp only [torsionCoeffWeilPairing_apply _ _ _ hm.natCast_ne_zero_of_algebra]
  exact Isogeny.neg_weilPairing _ _ _ _ _

variable {W} in
/-- **The Weil pairing of two distinct points of order two is `-1`**: on `E(Kˢ)[2]`, for `2`
invertible in `K`, `e₂(T, S)` is the nontrivial element of `μ₂` whenever `T` and `S` are distinct
and nonzero. -/
theorem torsionCoeffWeilPairing_two_eq_mu2NegOne (h2 : IsUnit ((2 : ℕ) : K))
    {T S : W.TorsionCoeff 2} (hT : T ≠ 0) (hS : S ≠ 0) (hTS : T ≠ S) :
    W.torsionCoeffWeilPairing 2 h2 T S = mu2NegOne := by
  have := W.isAddKleinFour_torsionCoeff_two h2
  refine (eq_zero_or_eq_mu2NegOne _).resolve_left fun h ↦ hT ?_
  refine W.torsionCoeffWeilPairing_nondegenerate 2 h2 fun Q ↦ ?_
  by_cases hQ : Q = 0
  · rw [hQ, map_zero]
  by_cases hQT : Q = T
  · rw [hQT, torsionCoeffWeilPairing_self]
  by_cases hQS : Q = S
  · rw [hQS, h]
  rw [IsAddKleinFour.eq_add_of_ne_all hT hS hTS hQ hQT hQS, map_add, h,
    torsionCoeffWeilPairing_self, add_zero]

/-- **Pairing with a sum of points of order two.** For a family `m` of square roots of unity
indexed by `E(Kˢ)[2]`, the sum of the points `T` with `m T ≠ 0` pairs with a nonzero point `S` to
`∑ T, m T - m O - m S`, as two distinct nonzero points of order two pair to `-1`. -/
theorem torsionCoeffWeilPairing_sum_ite (h2 : IsUnit ((2 : ℕ) : K))
    [Fintype (W.TorsionCoeff 2)] (m : W.TorsionCoeff 2 → KummerCoeff K 2)
    [DecidablePred (m · = 0)] {S : W.TorsionCoeff 2} (hS : S ≠ 0) :
    W.torsionCoeffWeilPairing 2 h2 (∑ T, if m T = 0 then 0 else T) S =
      (∑ T, m T) - m 0 - m S := by
  classical
  have hterm (T : W.TorsionCoeff 2) :
      W.torsionCoeffWeilPairing 2 h2 (if m T = 0 then 0 else T) S =
        m T - (if T = 0 then m T else 0) - (if T = S then m T else 0) := by
    by_cases hT0 : T = 0
    · simp [hT0, Ne.symm hS]
    by_cases hTS : T = S
    · subst hTS
      rcases eq_or_ne (m T) 0 with h | h <;> simp [h, hS]
    simp only [hT0, hTS, ↓reduceIte, sub_zero]
    have : Invertible (2 : K) := (by simpa using h2 : IsUnit (2 : K)).invertible
    rcases eq_zero_or_eq_mu2NegOne (m T) with h | h
    · simp [h]
    · simp only [h, mu2NegOne_ne_zero, ↓reduceIte]
      exact WeierstrassCurve.torsionCoeffWeilPairing_two_eq_mu2NegOne h2 hT0 hS hTS
  simp only [map_sum, AddMonoidHom.finsetSum_apply, hterm, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

include hm in
/-- If `G_K` fixes every point of `E(Kˢ)[m]`, it fixes every `m`-th root of unity: these are
values of the Weil pairing, which is equivariant. -/
private theorem smul_kummerCoeff_eq_self_of_forall_smul_eq_self
    (h : ∀ (σ : AbsoluteGaloisGroup K) (P : W.TorsionCoeff m), σ • P = P)
    (σ : AbsoluteGaloisGroup K) (x : KummerCoeff K m) : σ • x = x := by
  classical
  have := hm.neZero_natCast
  have hσ : W.torsionGaloisAction m σ = 1 := by
    refine Multiplicative.toAdd.injective (AddEquiv.ext fun P ↦ ?_)
    have := W.torsionByCongr_pointCoeffEquiv_symm_smul σ
      (AddEquiv.torsionByCongr W.pointCoeffEquiv m P)
    rw [h, AddEquiv.symm_apply_apply] at this
    exact this.symm
  refine Additive.toMul.injective <| Subtype.ext <| Units.ext ?_
  simpa [AlgEquiv.smul_units_def] using
    W.algEquiv_apply_eq_self_of_torsionGaloisAction_eq_one
      hm.natCast_ne_zero_of_algebra hσ
      (ζ := ((x.toMul : (SeparableClosure K)ˣ) : SeparableClosure K))
      (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 x.toMul.2, Units.val_one])

/-! ### Change of field -/

section BaseChange

variable {L : Type*} [Field L] [Algebra K L] (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

omit [W.IsElliptic] in
/-- The base change of `W` to `Kˢ`, transported along `τ : Kˢ → Lˢ`, is the base change of `W⁄L`
to `Lˢ`. -/
private theorem map_baseChange_separableClosure :
    (W⁄(SeparableClosure K)).map (τ : SeparableClosure K →+* SeparableClosure L) =
      (W⁄L)⁄(SeparableClosure L) :=
  (map_baseChange W τ).trans
    (map_baseChange W (IsScalarTower.toAlgHom K L (SeparableClosure L))).symm

omit [W.IsElliptic] in
open scoped Classical in
/-- The map `E(Kˢ)[m] → E(Lˢ)[m]` induced by `τ` is `WeierstrassCurve.torsionMapAlong`, read
through the identifications of the coefficient modules with the points of the base changes. -/
private theorem torsionByCongr_symm_torsionCoeffBaseChange (P : W.TorsionCoeff m) :
    (AddEquiv.torsionByCongr (W⁄L).pointCoeffEquiv m).symm (W.torsionCoeffBaseChange τ m P) =
      AddEquiv.torsionByCongr
        (AddEquiv.cast (M := fun V : WeierstrassCurve (SeparableClosure L) ↦ V.toAffine.Point)
          (W.map_baseChange_separableClosure τ)) m
        ((W⁄(SeparableClosure K)).torsionMapAlong
          (τ : SeparableClosure K →+* SeparableClosure L) m
          ((AddEquiv.torsionByCongr W.pointCoeffEquiv m).symm P)) := by
  apply Subtype.ext
  obtain ⟨P, hP⟩ := P
  obtain ⟨P, rfl⟩ := W.pointCoeffEquiv.surjective P
  simp only [AddEquiv.torsionByCongr_symm_apply_coe, AddEquiv.torsionByCongr_apply_coe,
    coe_torsionCoeffBaseChange, coe_torsionMapAlong_apply, AddEquiv.symm_apply_apply]
  rcases P with _ | ⟨x, y, h⟩
  · rw [← Affine.Point.zero_def, map_zero, map_zero, Affine.Point.mapAlong_zero, map_zero,
      map_zero]
  · rw [pointCoeffBaseChange_pointCoeffEquiv_some, AddEquiv.symm_apply_apply,
      Affine.Point.mapAlong_some, AddEquiv.cast_apply,
      Affine.Point.cast_some (W.map_baseChange_separableClosure τ)]
    simp

variable {m}

/-- The torsion Weil pairing commutes with field extension at propositionally equal levels.
The hypotheses specify the underlying images of the points, and values are compared in the
ambient separable closure to avoid casts between the roots-of-unity subgroups. -/
theorem coe_torsionCoeffWeilPairing_baseChange (n : ℕ) (hn : IsUnit (n : L)) (hmn : n = m)
    (P Q : W.TorsionCoeff m) (P' Q' : (W⁄L).TorsionCoeff n)
    (hP : (P' : (W⁄L).PointCoeff) = W.pointCoeffBaseChange τ P)
    (hQ : (Q' : (W⁄L).PointCoeff) = W.pointCoeffBaseChange τ Q) :
    ((W⁄L).torsionCoeffWeilPairing n hn P' Q').toMul.val.val =
      τ ((W.torsionCoeffWeilPairing m hm P Q).toMul.val.val) := by
  subst n
  have hP' : P' = W.torsionCoeffBaseChange τ m P :=
    Subtype.ext (by simpa only [coe_torsionCoeffBaseChange] using hP)
  have hQ' : Q' = W.torsionCoeffBaseChange τ m Q :=
    Subtype.ext (by simpa only [coe_torsionCoeffBaseChange] using hQ)
  rw [hP', hQ', W.torsionCoeffWeilPairing_torsionCoeffBaseChange hm τ P Q]
  simp only [toMul_kummerCoeffBaseChange, Units.coe_map, MonoidHom.coe_ofClass]

end BaseChange

/-! ### The coefficient map attached to a rational torsion point -/

section Rational

variable [DecidableEq K]

/-! ### Restriction to a field extension -/

section Restriction

variable {L : Type*} [Field L] [Algebra K L] [DecidableEq L]
  (τ : SeparableClosure K →ₐ[K] SeparableClosure L)

end Restriction

/-! ### Detecting classes when `E[m]` is rational -/

end Rational

end WeierstrassCurve
