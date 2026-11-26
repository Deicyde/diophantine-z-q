module

public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.Tactic.Ring

/-! # The degree-zero algebra on the short Weierstrass locus -/

@[expose] public section

namespace RC.ModelInvariants.ShortWeierstrass

open MvPolynomial HomogeneousLocalization
open scoped BigOperators

noncomputable section

variable (R : Type*) [CommRing R]

/-- The two Weierstrass coefficients have weights four and six, respectively. -/
def weights : Bool → ℕ := fun i => if i then 6 else 4

abbrev coefficientGrading := weightedHomogeneousSubmodule R weights

instance : GradedAlgebra (coefficientGrading R) := weightedGradedAlgebra R weights

/-- The discriminant of the short Weierstrass equation. -/
def discriminant : MvPolynomial Bool R :=
  C (-16 : R) * (C (4 : R) * X false ^ 3 + C (27 : R) * X true ^ 2)

theorem a4_cubed_mem : (X false ^ 3 : MvPolynomial Bool R) ∈ coefficientGrading R 12 :=
  (isWeightedHomogeneous_X R weights false).pow 3

theorem a6_squared_mem : (X true ^ 2 : MvPolynomial Bool R) ∈ coefficientGrading R 12 :=
  (isWeightedHomogeneous_X R weights true).pow 2

theorem discriminant_mem : discriminant R ∈ coefficientGrading R 12 := by
  have h4 : IsWeightedHomogeneous weights (X false ^ 3 : MvPolynomial Bool R) 12 := a4_cubed_mem R
  have h6 : IsWeightedHomogeneous weights (X true ^ 2 : MvPolynomial Bool R) 12 := a6_squared_mem R
  exact ((h4.C_mul 4).add (h6.C_mul 27)).C_mul (-16)

/-- This homogeneous localization consists of fractions (s/\Delta^n) with (s) of weight
(12n). It is the degree-zero ring of the discriminant-open chart. -/
abbrev CoordinateRing := HomogeneousLocalization.Away (coefficientGrading R) (discriminant R)

instance : Algebra R (CoordinateRing R) :=
  ((algebraMap (coefficientGrading R 0) (CoordinateRing R)).comp
    (algebraMap R (coefficientGrading R 0))).toAlgebra

instance : IsScalarTower R (coefficientGrading R 0) (MvPolynomial Bool R) :=
  IsScalarTower.of_algebraMap_eq
    (R := R) (S := coefficientGrading R 0) (A := MvPolynomial Bool R) fun _ => rfl

/-- The degree-zero fraction (a_4^3/\Delta). -/
def a4Ratio : CoordinateRing R :=
  Away.mk (coefficientGrading R) (discriminant_mem R) 1 (X false ^ 3) (a4_cubed_mem R)

/-- The degree-zero fraction (a_6^2/\Delta). -/
def a6Ratio : CoordinateRing R :=
  Away.mk (coefficientGrading R) (discriminant_mem R) 1 (X true ^ 2) (a6_squared_mem R)

set_option maxHeartbeats 800000 in
/-- The two indicated fractions generate the degree-zero algebra, over any base ring. -/
theorem ratios_generate :
    Algebra.adjoin R ({a4Ratio R, a6Ratio R} : Set (CoordinateRing R)) = ⊤ := by
  classical
  let A := Algebra.adjoin R ({a4Ratio R, a6Ratio R} : Set (CoordinateRing R))
  have h4 : a4Ratio R ∈ A := Algebra.subset_adjoin (by simp)
  have h6 : a6Ratio R ∈ A := Algebra.subset_adjoin (by simp)
  have hgen : Algebra.adjoin (coefficientGrading R 0) (Set.range (X : Bool → MvPolynomial Bool R)) =
      ⊤ := by
    have hle : Algebra.adjoin R (Set.range (X : Bool → MvPolynomial Bool R)) ≤
        (Algebra.adjoin (coefficientGrading R 0) (Set.range X)).restrictScalars R :=
      Algebra.adjoin_le fun _ hx => Algebra.subset_adjoin hx
    rw [MvPolynomial.adjoin_range_X] at hle
    exact Algebra.eq_top_iff.2 fun x => hle (Algebra.mem_top (x := x))
  have span_all := Away.span_mk_prod_pow_eq_top (discriminant_mem R) (X : Bool → MvPolynomial Bool R)
    hgen weights (fun i => isWeightedHomogeneous_X R weights i)
  apply eq_top_iff.2
  intro x _
  change x ∈ A
  have hx : x ∈ _ := show x ∈ (⊤ : Submodule (coefficientGrading R 0) (CoordinateRing R)) from trivial
  rw [← span_all] at hx
  refine Submodule.span_induction (p := fun y _ => y ∈ A) ?_ (zero_mem A)
    (fun _ _ _ _ hy hz => add_mem hy hz) ?_ hx
  · rintro _ ⟨n, exponents, hweight, rfl⟩
    have h : 4 * exponents false + 6 * exponents true = 12 * n := by
      simpa [Fintype.sum_bool, weights, mul_comm, add_comm] using hweight
    have he4 : exponents false = 3 * (exponents false / 3) := by omega
    have he6 : exponents true = 2 * (exponents true / 2) := by omega
    have hen : n = exponents false / 3 + exponents true / 2 := by omega
    have he :
        Away.mk (coefficientGrading R) (discriminant_mem R) n
          (∏ i, X i ^ exponents i)
          (hweight ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ =>
            isWeightedHomogeneous_X R weights i) =
          a4Ratio R ^ (exponents false / 3) * a6Ratio R ^ (exponents true / 2) := by
      apply HomogeneousLocalization.val_injective
      simp only [Away.val_mk, val_mul, val_pow, a4Ratio, a6Ratio, Localization.mk_pow,
        Localization.mk_mul, pow_one, Fintype.prod_bool]
      congr 1
      · rw [← pow_mul, ← pow_mul, ← he4, ← he6, mul_comm]
      · apply Subtype.ext
        change discriminant R ^ n =
          discriminant R ^ (exponents false / 3) * discriminant R ^ (exponents true / 2)
        rw [hen, pow_add]
    rw [he]
    exact mul_mem (pow_mem h4 _) (pow_mem h6 _)
  · intro r y _ hy
    rw [Algebra.smul_def]
    apply mul_mem _ hy
    have hr : (r : MvPolynomial Bool R) = C ((r : MvPolynomial Bool R).coeff 0) := by
      have hm : IsWeightedHomogeneous weights (r : MvPolynomial Bool R) 0 := r.property
      calc
        (r : MvPolynomial Bool R) = weightedHomogeneousComponent weights 0 r :=
          hm.weightedHomogeneousComponent_same.symm
        _ = C ((r : MvPolynomial Bool R).coeff 0) :=
          weightedHomogeneousComponent_zero _ (by intro i; cases i <;> decide)
    have hr' : r = algebraMap R (coefficientGrading R 0) ((r : MvPolynomial Bool R).coeff 0) :=
      Subtype.ext hr
    have he : algebraMap (coefficientGrading R 0) (CoordinateRing R) r =
        algebraMap R (CoordinateRing R) ((r : MvPolynomial Bool R).coeff 0) :=
      congrArg (algebraMap (coefficientGrading R 0) (CoordinateRing R)) hr'
    rw [he]
    exact algebraMap_mem A _

/-- The short Weierstrass (j)-invariant (c_4^3/\Delta), with (c_4=-48a_4). -/
def j : CoordinateRing R := algebraMap R (CoordinateRing R) ((-48 : R) ^ 3) * a4Ratio R

private abbrev LocalizedRing := Localization.Away (discriminant R)

private def localizationInclusion : CoordinateRing R →ₐ[R] LocalizedRing R where
  __ := algebraMap (CoordinateRing R) (LocalizedRing R)
  commutes' _ := rfl

private theorem discriminant_expand :
    discriminant R = C (-64 : R) * X false ^ 3 + C (-432 : R) * X true ^ 2 := by
  simp only [discriminant, mul_add, ← mul_assoc, ← map_mul]
  norm_num

private theorem fraction_mul_denominator (n : ℕ) (a : MvPolynomial Bool R)
    (ha : a ∈ coefficientGrading R (n • 12)) :
    (Away.mk (coefficientGrading R) (discriminant_mem R) n a ha).val *
      algebraMap (MvPolynomial Bool R) (LocalizedRing R) (discriminant R ^ n) =
      algebraMap (MvPolynomial Bool R) (LocalizedRing R) a := by
  rw [Away.val_mk, Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec (LocalizedRing R) a
    (⟨discriminant R ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers (discriminant R))

/-- The sole linear relation needed to eliminate the second fractional generator. -/
theorem ratios_relation :
    algebraMap R (CoordinateRing R) (-64) * a4Ratio R +
      algebraMap R (CoordinateRing R) (-432) * a6Ratio R = 1 := by
  apply HomogeneousLocalization.val_injective
  let a := algebraMap (MvPolynomial Bool R) (LocalizedRing R)
  apply (IsLocalization.Away.algebraMap_isUnit (S := LocalizedRing R) (discriminant R)).mul_left_inj.1
  simp only [val_add, val_mul, val_one, add_mul, mul_assoc, one_mul]
  have h4 : (a4Ratio R).val * a (discriminant R) = a (X false ^ 3) := by
    simpa only [a4Ratio, pow_one, a] using
      fraction_mul_denominator R 1 (X false ^ 3) (a4_cubed_mem R)
  have h6 : (a6Ratio R).val * a (discriminant R) = a (X true ^ 2) := by
    simpa only [a6Ratio, pow_one, a] using
      fraction_mul_denominator R 1 (X true ^ 2) (a6_squared_mem R)
  change a (C (-64 : R)) * ((a4Ratio R).val * a (discriminant R)) +
    a (C (-432 : R)) * ((a6Ratio R).val * a (discriminant R)) = a (discriminant R)
  rw [h4, h6, ← map_mul, ← map_mul, ← map_add]
  exact congrArg a (discriminant_expand R).symm

private theorem isUnit_a6Coefficient (h : IsUnit (6 : R)) : IsUnit (-432 : R) :=
  isUnit_of_dvd_unit ⟨-3, by norm_num⟩ (h.pow 4)

private theorem isUnit_jCoefficient (h : IsUnit (6 : R)) : IsUnit ((-48 : R) ^ 3) :=
  (isUnit_of_dvd_unit (show (-48 : R) ∣ (6 : R) ^ 4 from ⟨-27, by norm_num⟩) (h.pow 4)).pow 3

private theorem aeval_j_surjective (h : IsUnit (6 : R)) :
    Function.Surjective (Polynomial.aeval (R := R) (j R)) := by
  let A := (Polynomial.aeval (R := R) (j R)).range
  have hj : j R ∈ A := ⟨Polynomial.X, Polynomial.aeval_X _⟩
  let c := isUnit_jCoefficient R h
  let b := isUnit_a6Coefficient R h
  have h4 : a4Ratio R ∈ A := by
    have he : algebraMap R (CoordinateRing R) (↑c.unit⁻¹ : R) * j R = a4Ratio R := by
      rw [j, ← mul_assoc, ← map_mul, c.val_inv_mul, map_one, one_mul]
    rw [← he]
    exact mul_mem (algebraMap_mem A _) hj
  have h6 : a6Ratio R ∈ A := by
    have he : algebraMap R (CoordinateRing R) (-432) * a6Ratio R =
        1 - algebraMap R (CoordinateRing R) (-64) * a4Ratio R := by
      rw [← ratios_relation R]
      ring
    have he' := congrArg (algebraMap R (CoordinateRing R) (↑b.unit⁻¹ : R) * ·) he
    rw [← mul_assoc, ← map_mul, b.val_inv_mul, map_one, one_mul] at he'
    rw [he']
    exact mul_mem (algebraMap_mem A _) (sub_mem (one_mem A) (mul_mem (algebraMap_mem A _) h4))
  apply (AlgHom.range_eq_top _).1
  rw [← top_le_iff, ← ratios_generate R]
  apply Algebra.adjoin_le
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · exact h4
  · exact h6

private theorem adjoinRoot_pow {A : Type*} [CommRing A] (n : ℕ) (a : A) :
    AdjoinRoot.root (Polynomial.X ^ n - Polynomial.C a) ^ n =
      algebraMap A (AdjoinRoot (Polynomial.X ^ n - Polynomial.C a)) a := by
  apply sub_eq_zero.mp
  have he := AdjoinRoot.eval₂_root (Polynomial.X ^ n - Polynomial.C a)
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at he
  exact he

private theorem adjoinRoot_pow_algebraMap_injective {A : Type*} [CommRing A] [Nontrivial A]
    {n : ℕ} (hn : 0 < n) (a : A) :
    Function.Injective (algebraMap A (AdjoinRoot (Polynomial.X ^ n - Polynomial.C a))) :=
  AdjoinRoot.of.injective_of_monic_of_degree_pos
    (Polynomial.monic_X_pow_sub_C a hn.ne') (by
      rw [Polynomial.degree_X_pow_sub_C hn]
      exact_mod_cast hn)

set_option maxHeartbeats 1000000 in
private theorem aeval_j_injective (h : IsUnit (6 : R)) :
    Function.Injective (Polynomial.aeval (R := R) (j R)) := by
  by_cases htriv : Subsingleton R
  · let : Subsingleton R := htriv
    exact Function.injective_of_subsingleton _
  let : Nontrivial R := not_subsingleton_iff_nontrivial.mp htriv
  let c := isUnit_jCoefficient R h
  let b := isUnit_a6Coefficient R h
  let p : Polynomial (Polynomial R) :=
    Polynomial.X ^ 3 - Polynomial.C (Polynomial.C (↑c.unit⁻¹ : R) * Polynomial.X)
  let A := AdjoinRoot p
  have hA : Function.Injective (algebraMap (Polynomial R) A) :=
    adjoinRoot_pow_algebraMap_injective (by decide : 0 < 3) _
  let : Nontrivial A := hA.nontrivial
  let z := AdjoinRoot.root p
  let q : Polynomial A :=
    Polynomial.X ^ 2 - Polynomial.C
      (algebraMap R A (↑b.unit⁻¹ : R) * (1 - algebraMap R A (-64) * z ^ 3))
  let T := AdjoinRoot q
  have hT : Function.Injective (algebraMap A T) :=
    adjoinRoot_pow_algebraMap_injective (by decide : 0 < 2) _
  let x4 := algebraMap A T z
  let x6 := AdjoinRoot.root q
  have h4 : algebraMap R T ((-48 : R) ^ 3) * x4 ^ 3 =
      algebraMap (Polynomial R) T Polynomial.X := by
    have he := adjoinRoot_pow 3 (Polynomial.C (↑c.unit⁻¹ : R) * Polynomial.X)
    change z ^ 3 = algebraMap (Polynomial R) A _ at he
    rw [show x4 ^ 3 = algebraMap A T (z ^ 3) from (map_pow _ _ _).symm, he]
    rw [← IsScalarTower.algebraMap_apply (Polynomial R) A T, map_mul]
    change algebraMap R T ((-48 : R) ^ 3) *
      (algebraMap (Polynomial R) T (algebraMap R (Polynomial R) (↑c.unit⁻¹ : R)) *
        algebraMap (Polynomial R) T Polynomial.X) = _
    rw [← IsScalarTower.algebraMap_apply R (Polynomial R) T, ← mul_assoc, ← map_mul,
      mul_comm ((-48 : R) ^ 3),
      c.val_inv_mul, map_one, one_mul]
  have h6 : algebraMap R T (-432) * x6 ^ 2 = 1 - algebraMap R T (-64) * x4 ^ 3 := by
    have he := adjoinRoot_pow 2 (algebraMap R A (↑b.unit⁻¹ : R) *
      (1 - algebraMap R A (-64) * z ^ 3))
    change x6 ^ 2 = algebraMap A T _ at he
    rw [he]
    simp only [map_mul, map_sub, map_one, map_pow, ← IsScalarTower.algebraMap_apply R A T]
    rw [← mul_assoc, ← map_mul, mul_comm (-432 : R), b.val_inv_mul, map_one, one_mul]
  let f : MvPolynomial Bool R →ₐ[R] T := MvPolynomial.aeval fun i => if i then x6 else x4
  have hδ : f (discriminant R) = 1 := by
    rw [discriminant_expand]
    simp only [f, map_add, map_mul, map_pow, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Bool.false_eq_true, ite_false, ite_true]
    rw [h6]
    ring
  have hδunit : IsUnit (f (discriminant R)) := hδ ▸ isUnit_one
  let lift : LocalizedRing R →ₐ[R] T := IsLocalization.Away.liftAlgHom (discriminant R) hδunit
  let F := lift.comp (localizationInclusion R)
  have hfrac : F (a4Ratio R) = x4 ^ 3 := by
    have he : (a4Ratio R).val * algebraMap (MvPolynomial Bool R) (LocalizedRing R)
        (discriminant R) = algebraMap (MvPolynomial Bool R) (LocalizedRing R) (X false ^ 3) := by
      simpa only [a4Ratio, pow_one] using
        fraction_mul_denominator R 1 (X false ^ 3) (a4_cubed_mem R)
    have hl := congrArg lift he
    change lift _ = lift _ at hl
    rw [map_mul] at hl
    simp only [lift, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq, map_pow] at hl
    change F (a4Ratio R) * f (discriminant R) = f (X false) ^ 3 at hl
    rw [hδ, mul_one, show f (X false) = x4 from MvPolynomial.aeval_X _ _] at hl
    exact hl
  have he : F.comp (Polynomial.aeval (j R)) = IsScalarTower.toAlgHom R (Polynomial R) T := by
    apply Polynomial.algHom_ext
    rw [AlgHom.comp_apply, Polynomial.aeval_X, j, map_mul, F.commutes, hfrac]
    exact h4
  have hcomp : Function.Injective (F.comp (Polynomial.aeval (R := R) (j R))) := by
    rw [he]
    exact hT.comp hA
  intro x y hxy
  exact hcomp (congrArg F hxy)

/-- When six is invertible, the coordinate ring of the short Weierstrass quotient is
a polynomial algebra on the displayed (j)-invariant. -/
@[no_expose] noncomputable def jEquiv (h : IsUnit (6 : R)) :
    Polynomial R ≃ₐ[R] CoordinateRing R :=
  AlgEquiv.ofBijective (Polynomial.aeval (j R)) ⟨aeval_j_injective R h, aeval_j_surjective R h⟩

theorem jEquiv_X (h : IsUnit (6 : R)) :
    jEquiv R h Polynomial.X = j R := Polynomial.aeval_X _

/-- Point maps out of the degree-zero ring are identified by the value of (j). -/
noncomputable def jPoints {K : Type*} [CommRing K] [Algebra R K]
    (h : IsUnit (6 : R)) : (CoordinateRing R →ₐ[R] K) ≃ K where
  toFun f := f (j R)
  invFun x := (Polynomial.aeval x).comp (jEquiv R h).symm.toAlgHom
  left_inv f := by
    change (Polynomial.aeval (f (j R))).comp (jEquiv R h).symm.toAlgHom = f
    have he : Polynomial.aeval (f (j R)) = f.comp (jEquiv R h).toAlgHom := by
      apply Polynomial.algHom_ext
      rw [Polynomial.aeval_X, AlgHom.comp_apply]
      exact congrArg f (jEquiv_X R h).symm
    rw [he, AlgHom.comp_assoc]
    simp
  right_inv x := by
    change Polynomial.aeval x ((jEquiv R h).symm (j R)) = x
    rw [← jEquiv_X R h, AlgEquiv.symm_apply_apply, Polynomial.aeval_X]

theorem jPoints_apply {K : Type*} [CommRing K] [Algebra R K] (h : IsUnit (6 : R))
    (f : CoordinateRing R →ₐ[R] K) : jPoints R h f = f (j R) := rfl

#print axioms localizationInclusion
#print axioms discriminant_expand
#print axioms fraction_mul_denominator
#print axioms ratios_relation
#print axioms isUnit_a6Coefficient
#print axioms isUnit_jCoefficient
#print axioms aeval_j_surjective
#print axioms adjoinRoot_pow
#print axioms adjoinRoot_pow_algebraMap_injective
#print axioms aeval_j_injective
#print axioms jEquiv
#print axioms jEquiv_X
#print axioms jPoints
#print axioms jPoints_apply

#print axioms weights
#print axioms coefficientGrading
#print axioms discriminant
#print axioms CoordinateRing
#print axioms a4Ratio
#print axioms a6Ratio
#print axioms j
#print axioms discriminant_mem
#print axioms a4_cubed_mem
#print axioms a6_squared_mem
#print axioms ratios_generate

end

end RC.ModelInvariants.ShortWeierstrass
