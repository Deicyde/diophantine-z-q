import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ExactOrderScaling
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.WeightedPresentation
import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.LaurentWeights
import Mathlib.Algebra.Group.Int.TypeTags

/-! # The grading of the short exact-order cover -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion LaurentPolynomial

private noncomputable def laurentUnits (k : Type*) [Field k] :
    Multiplicative ℤ →* (LaurentPolynomial k)ˣ where
  toFun i :=
    ⟨T i.toAdd, T (-i.toAdd), by rw [← T_add, add_neg_cancel, T_zero],
      by rw [← T_add, neg_add_cancel, T_zero]⟩
  map_one' := Units.ext T_zero
  map_mul' i j := Units.ext (T_add _ _)

private theorem laurentUnit_zpow (k : Type*) [Field k] (i : ℤ) :
    ((Units.map (algebraMap (LaurentPolynomial k) (FractionRing (LaurentPolynomial k)))
      (laurentUnits k (Multiplicative.ofAdd 1)) : (FractionRing (LaurentPolynomial k))ˣ) :
      FractionRing (LaurentPolynomial k)) ^ i =
      algebraMap (LaurentPolynomial k) (FractionRing (LaurentPolynomial k)) (T i) := by
  have he : (Multiplicative.ofAdd 1 : Multiplicative ℤ) ^ i = Multiplicative.ofAdd i := by
    rw [← Int.ofAdd_mul, one_mul]
  rw [← Units.val_zpow_eq_zpow_val, ← map_zpow, ← map_zpow, he]
  rfl

section Cover

universe u

variable {R : Type u} [CommRing R] {n : ℕ} (hn : IsUnit ((n + 2 : ℕ) : ShortBase R))
  [Algebra R (ExactOrderAlgebra (shortFamily R) hn)]
  [IsScalarTower R (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn)]

/-- The grade of each polynomial generator is fixed by the weights
`4, 6, 2, 3, -12` on the two coefficients, the point and the inverse
discriminant. -/
noncomputable def shortExactOrderGrading :
    ℤ → Submodule R (ExactOrderAlgebra (shortFamily R) hn) :=
  presentationWeight shortCoordinateWeight (exactOrderShortPresentation hn)

/-- The image of a named coordinate lies in its prescribed degree. -/
theorem shortExactOrderCoordinates_mem (i : Fin 5) :
    exactOrderShortCoordinates hn i ∈ shortExactOrderGrading hn (shortCoordinateWeight i) :=
  ⟨MvPolynomial.X i, MvPolynomial.isWeightedHomogeneous_X R shortCoordinateWeight i,
    MvPolynomial.aeval_X _ _⟩

/-- The discriminant is a unit of degree twelve on the short exact-order
cover. -/
theorem shortExactOrderDiscriminant_mem :
    algebraMap (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn) (shortFamily R).Δ ∈
      shortExactOrderGrading hn 12 := by
  let W := shortFamily R
  let S := ExactOrderAlgebra W hn
  let : W.IsShortNF := shortFamily_IsShortNF
  have hx : algebraMap (ShortBase R) S W.a₄ ∈ shortExactOrderGrading hn 4 :=
    shortExactOrderCoordinates_mem hn 0
  have hy : algebraMap (ShortBase R) S W.a₆ ∈ shortExactOrderGrading hn 6 :=
    shortExactOrderCoordinates_mem hn 1
  letI : SetLike.GradedMonoid (shortExactOrderGrading hn) :=
    presentationWeightMonoid _ _
  have hx' : (algebraMap (ShortBase R) S W.a₄) ^ 3 ∈ shortExactOrderGrading hn 12 :=
    SetLike.pow_mem_graded 3 hx
  have hy' : (algebraMap (ShortBase R) S W.a₆) ^ 2 ∈ shortExactOrderGrading hn 12 :=
    SetLike.pow_mem_graded 2 hy
  change algebraMap (ShortBase R) S W.Δ ∈ _
  rw [W.Δ_of_isShortNF, map_mul, map_add, map_mul, map_mul, map_pow, map_pow]
  simp only [map_ofNat, map_neg]
  have h (a : ℤ) {x : S} (hx : x ∈ shortExactOrderGrading hn 12) :
      (a : S) * x ∈ shortExactOrderGrading hn 12 := by
    simpa only [Algebra.smul_def, map_intCast] using
      (shortExactOrderGrading hn 12).smul_mem (a : R) hx
  exact h (-16) (add_mem (h 4 hx') (h 27 hy'))

private theorem weightedLaurentEval_of_mem {k : Type*} [Field k] [Algebra R k]
    (a : Fin 5 → k) (p : MvPolynomial (Fin 5) R) (i : ℤ)
    (hp : p ∈ MvPolynomial.weightedHomogeneousSubmodule R shortCoordinateWeight i) :
    weightedLaurentEval shortCoordinateWeight a p =
      LaurentPolynomial.C (MvPolynomial.aeval a p) * T i := by
  ext j
  rw [weightedLaurentEval_coeff, MvPolynomial.weightedHomogeneousComponent_of_mem hp,
    ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- Geometric scaling evaluates a homogeneous element with its grade. -/
theorem scaleShortExactOrderPoint_homogeneous {k : Type*} [Field k] [Algebra R k]
    [DecidableEq k] (u : kˣ) (f : ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k)
    {i : ℤ} {x : ExactOrderAlgebra (shortFamily R) hn} (hx : x ∈ shortExactOrderGrading hn i) :
    scaleShortExactOrderPoint hn u f x = (u : k) ^ i * f x := by
  obtain ⟨p, hp, rfl⟩ := hx
  let g := scaleShortExactOrderPoint hn u f
  let a : Fin 5 → k := fun j => f (exactOrderShortCoordinates hn j)
  let ev : LaurentPolynomial k →ₐ[R] k :=
    { LaurentPolynomial.eval₂ (RingHom.id k) u with
      commutes' := fun r => by
        change LaurentPolynomial.eval₂ (RingHom.id k) u (algebraMap R (LaurentPolynomial k) r) = _
        rw [LaurentPolynomial.algebraMap_apply, LaurentPolynomial.eval₂_C, RingHom.id_apply] }
  have he : g.comp (exactOrderShortPresentation hn) =
      ev.comp (weightedLaurentEval shortCoordinateWeight a) := by
    ext j
    simp only [AlgHom.comp_apply, exactOrderShortPresentation, weightedLaurentEval,
      MvPolynomial.aeval_X]
    change g (exactOrderShortCoordinates hn j) =
      LaurentPolynomial.eval₂ (RingHom.id k) u (LaurentPolynomial.C (a j) * T (shortCoordinateWeight j))
    rw [LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply, Units.val_zpow_eq_zpow_val, mul_comm]
    exact scaleShortExactOrderPoint_coordinates hn u f j
  have hf : f.comp (exactOrderShortPresentation hn) = MvPolynomial.aeval a := by
    ext j
    simp [exactOrderShortPresentation, a]
  change g (exactOrderShortPresentation hn p) = _ * f (exactOrderShortPresentation hn p)
  rw [← AlgHom.comp_apply, he, AlgHom.comp_apply, weightedLaurentEval_of_mem a p i hp,
    ← AlgHom.comp_apply, hf]
  change LaurentPolynomial.eval₂ (RingHom.id k) u _ = _
  rw [LaurentPolynomial.eval₂_C_mul_T, RingHom.id_apply, Units.val_zpow_eq_zpow_val, mul_comm]

private theorem scale_test_coordinate {k : Type*} [Field k] [Algebra R k] [DecidableEq k]
    (f : ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k) (j : Fin 5) :
    let L := FractionRing (LaurentPolynomial k)
    let e : k →ₐ[R] L := IsScalarTower.toAlgHom R k L
    let u := Units.map (algebraMap (LaurentPolynomial k) L) (laurentUnits k (Multiplicative.ofAdd 1))
    scaleShortExactOrderPoint hn u (e.comp f) (exactOrderShortCoordinates hn j) =
      algebraMap (LaurentPolynomial k) L
        (LaurentPolynomial.C (f (exactOrderShortCoordinates hn j)) * T (shortCoordinateWeight j)) := by
  classical
  intro L e u
  rw [scaleShortExactOrderPoint_coordinates, laurentUnit_zpow, AlgHom.comp_apply,
    map_mul, LaurentPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply k
      (LaurentPolynomial k) L]
  exact mul_comm _ _

private theorem scale_test_presentation {k : Type*} [Field k] [Algebra R k] [DecidableEq k]
    (f : ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k) (p : MvPolynomial (Fin 5) R) :
    let L := FractionRing (LaurentPolynomial k)
    let e : k →ₐ[R] L := IsScalarTower.toAlgHom R k L
    let u := Units.map (algebraMap (LaurentPolynomial k) L) (laurentUnits k (Multiplicative.ofAdd 1))
    scaleShortExactOrderPoint hn u (e.comp f) (exactOrderShortPresentation hn p) =
      algebraMap (LaurentPolynomial k) L
        (weightedLaurentEval shortCoordinateWeight (fun j => f (exactOrderShortCoordinates hn j)) p) := by
  classical
  intro L e u
  have h : (scaleShortExactOrderPoint hn u (e.comp f)).comp (exactOrderShortPresentation hn) =
      (IsScalarTower.toAlgHom R (LaurentPolynomial k) L).comp
        (weightedLaurentEval shortCoordinateWeight (fun j => f (exactOrderShortCoordinates hn j))) := by
    ext j
    simp only [AlgHom.comp_apply, exactOrderShortPresentation, weightedLaurentEval,
      MvPolynomial.aeval_X]
    exact scale_test_coordinate hn f j
  exact DFunLike.congr_fun h p

variable [IsDomain (ShortBase R)]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Membership in a degree can be tested on the transcendental scaling
of every field-valued point of the reduced exact-order algebra. -/
theorem shortExactOrderGrading_mem_of_field_scaling
    {x : ExactOrderAlgebra (shortFamily R) hn} {i : ℤ}
    (h : ∀ (k : Type u) [Field k] [Algebra R k] [DecidableEq k]
      (u : kˣ) (f : ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k),
      scaleShortExactOrderPoint hn u f x = (u : k) ^ i * f x) :
    x ∈ shortExactOrderGrading hn i := by
  classical
  let : IsReduced (ExactOrderAlgebra (shortFamily R) hn) :=
    exactOrderAlgebra_isReduced (shortFamily R) hn
  obtain ⟨p, hp⟩ := exactOrderShortPresentation_surjective hn x
  refine ⟨MvPolynomial.weightedHomogeneousComponent shortCoordinateWeight i p,
    MvPolynomial.weightedHomogeneousComponent_mem _ p i, ?_⟩
  apply eq_of_eq_at_fields (A := R)
  intro k _ _ f
  let L := FractionRing (LaurentPolynomial k)
  let e : k →ₐ[R] L := IsScalarTower.toAlgHom R k L
  let u : Lˣ := Units.map (algebraMap (LaurentPolynomial k) L)
    (laurentUnits k (Multiplicative.ofAdd 1))
  let a : Fin 5 → k := fun j => f (exactOrderShortCoordinates hn j)
  have hz : weightedLaurentEval shortCoordinateWeight a p = LaurentPolynomial.C (f x) * T i := by
    apply IsFractionRing.injective (LaurentPolynomial k) L
    have hs : scaleShortExactOrderPoint hn u (e.comp f) (exactOrderShortPresentation hn p) =
        algebraMap (LaurentPolynomial k) L (weightedLaurentEval shortCoordinateWeight a p) :=
      scale_test_presentation hn f p
    rw [← hs, hp, h L u (e.comp f), laurentUnit_zpow, AlgHom.comp_apply, map_mul,
      LaurentPolynomial.C_eq_algebraMap, ← IsScalarTower.algebraMap_apply k
        (LaurentPolynomial k) L]
    exact mul_comm _ _
  have hf : f.comp (exactOrderShortPresentation hn) = MvPolynomial.aeval a := by
    ext j
    simp [exactOrderShortPresentation, a]
  change f (exactOrderShortPresentation hn
    (MvPolynomial.weightedHomogeneousComponent shortCoordinateWeight i p)) = f x
  rw [← AlgHom.comp_apply, hf, ← weightedLaurentEval_coeff, hz,
    ← LaurentPolynomial.single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same]

set_option backward.isDefEq.respectTransparency false in
/-- The kernel of the presentation of the short exact-order locus is
homogeneous. Field points over a transcendental Laurent fraction field
detect each coefficient by scaling the curve and its marked generator. -/
theorem shortExactOrderPresentation_kernel (p : MvPolynomial (Fin 5) R)
    (hp : exactOrderShortPresentation hn p = 0) (i : ℤ) :
    exactOrderShortPresentation hn
      (MvPolynomial.weightedHomogeneousComponent shortCoordinateWeight i p) = 0 := by
  let : IsReduced (ExactOrderAlgebra (shortFamily R) hn) :=
    exactOrderAlgebra_isReduced (shortFamily R) hn
  apply weightedKernel_of_scaled_fields shortCoordinateWeight (exactOrderShortCoordinates hn)
    _ p hp i
  intro k _ _ f
  classical
  let L := FractionRing (LaurentPolynomial k)
  let e : k →ₐ[R] L := IsScalarTower.toAlgHom R k L
  let u : Lˣ := Units.map (algebraMap (LaurentPolynomial k) L)
    (laurentUnits k (Multiplicative.ofAdd 1))
  exact ⟨scaleShortExactOrderPoint hn u (e.comp f), scale_test_coordinate hn f⟩

/-- The internal grading of the actual exact-order algebra, obtained
from the weighted polynomials by the homogeneous kernel theorem. -/
@[instance_reducible] noncomputable def shortExactOrderGradedAlgebra :
    GradedAlgebra (shortExactOrderGrading hn) :=
  presentationGradedAlgebra shortCoordinateWeight (exactOrderShortPresentation hn)
    (exactOrderShortPresentation_surjective hn) (shortExactOrderPresentation_kernel hn)

end Cover

#print axioms laurentUnits
#print axioms laurentUnit_zpow
#print axioms shortExactOrderGrading
#print axioms shortExactOrderCoordinates_mem
#print axioms shortExactOrderDiscriminant_mem
#print axioms weightedLaurentEval_of_mem
#print axioms scaleShortExactOrderPoint_homogeneous
#print axioms scale_test_coordinate
#print axioms scale_test_presentation
#print axioms shortExactOrderGrading_mem_of_field_scaling
#print axioms shortExactOrderPresentation_kernel
#print axioms shortExactOrderGradedAlgebra

end WeierstrassCurve.ModelLevels
