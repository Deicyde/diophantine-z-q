import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.FieldTests
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Testing weighted relations using a transcendental scaling unit -/

namespace WeierstrassCurve.ModelLevels

open MvPolynomial LaurentPolynomial

universe u

variable {R σ : Type*} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Substitution of each weighted coordinate by its value times the
corresponding power of the Laurent indeterminate. -/
noncomputable def weightedLaurentEval (w : σ → ℤ) (a : σ → S) :
    MvPolynomial σ R →ₐ[R] LaurentPolynomial S :=
  MvPolynomial.aeval fun i => LaurentPolynomial.C (a i) * T (w i)

private theorem weightedLaurentEval_monomial (w : σ → ℤ) (a : σ → S)
    (d : σ →₀ ℕ) (r : R) :
    weightedLaurentEval w a (monomial d r) =
      AddMonoidAlgebra.single (Finsupp.weight w d) (MvPolynomial.aeval a (monomial d r)) := by
  classical
  rw [weightedLaurentEval, aeval_monomial, aeval_monomial, LaurentPolynomial.algebraMap_apply,
    LaurentPolynomial.single_eq_C_mul_T, map_mul]
  simp_rw [mul_pow, ← map_pow, LaurentPolynomial.T_pow]
  rw [Finsupp.prod_mul, map_finsuppProd, mul_assoc]
  congr 1
  congr 1
  rw [Finsupp.weight_apply]
  change (∏ i ∈ d.support, (T ((d i : ℤ) * w i) : LaurentPolynomial S)) =
    T (∑ i ∈ d.support, d i • w i)
  simp_rw [nsmul_eq_mul]
  induction d.support using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, LaurentPolynomial.T_add]

/-- Taking the Laurent coefficient of a weight is evaluation of the
corresponding weighted component. -/
theorem weightedLaurentEval_coeff (w : σ → ℤ) (a : σ → S) (p : MvPolynomial σ R) (i : ℤ) :
    (weightedLaurentEval w a p).coeff i =
      MvPolynomial.aeval a (weightedHomogeneousComponent w i p) := by
  classical
  rw [weightedHomogeneousComponent_apply (w := w), map_sum]
  conv_lhs => rw [p.as_sum, map_sum]
  simp_rw [weightedLaurentEval_monomial, AddMonoidAlgebra.coeff_sum, Finset.sum_apply',
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_filter]

/-- Compare Laurent coefficients after testing every point over a field
and its extension by a transcendental unit. -/
theorem weightedKernel_of_scaled_fields [IsReduced S] (w : σ → ℤ) (a : σ → S)
    (hscale : ∀ (k : Type u) [Field k] [Algebra R k] (f : S →ₐ[R] k),
      ∃ g : S →ₐ[R] FractionRing (LaurentPolynomial k), ∀ j,
        g (a j) = algebraMap (LaurentPolynomial k) (FractionRing (LaurentPolynomial k))
          (LaurentPolynomial.C (f (a j)) * T (w j)))
    (p : MvPolynomial σ R) (hp : MvPolynomial.aeval a p = 0) (i : ℤ) :
    MvPolynomial.aeval a (weightedHomogeneousComponent w i p) = 0 := by
  apply eq_of_eq_at_fields (A := R)
  intro k _ _ f
  obtain ⟨g, hg⟩ := hscale k f
  let L := FractionRing (LaurentPolynomial k)
  have he : g.comp (MvPolynomial.aeval a) =
      (IsScalarTower.toAlgHom R (LaurentPolynomial k) L).comp
        (weightedLaurentEval w (fun j => f (a j))) := by
    ext j
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, weightedLaurentEval]
    change g (a j) = algebraMap (LaurentPolynomial k) L _
    exact hg j
  have hz : weightedLaurentEval w (fun j => f (a j)) p = 0 := by
    apply IsFractionRing.injective (LaurentPolynomial k) L
    change ((IsScalarTower.toAlgHom R (LaurentPolynomial k) L).comp
      (weightedLaurentEval w (fun j => f (a j)))) p = algebraMap (LaurentPolynomial k) L 0
    rw [← he, AlgHom.comp_apply, hp, map_zero, map_zero]
  have hf : f.comp (MvPolynomial.aeval a) = MvPolynomial.aeval (fun j => f (a j)) := by
    ext j
    simp
  rw [map_zero, ← AlgHom.comp_apply, hf, ← weightedLaurentEval_coeff w, hz]
  rfl

#print axioms weightedLaurentEval
#print axioms weightedLaurentEval_monomial
#print axioms weightedLaurentEval_coeff
#print axioms weightedKernel_of_scaled_fields

end WeierstrassCurve.ModelLevels
