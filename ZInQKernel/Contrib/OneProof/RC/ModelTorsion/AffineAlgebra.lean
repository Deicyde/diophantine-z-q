import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.AbscissaAlgebra
import Mathlib.RingTheory.Etale.Pi
import Mathlib.RingTheory.AlgebraTower
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # The algebra of nonidentity torsion in the affine chart -/

namespace WeierstrassCurve.ModelTorsion

open Polynomial
open WeierstrassCurve.Affine

universe u v

variable {A : Type u} [CommRing A]

/-- The Weierstrass equation as a monic polynomial in the ordinate. -/
noncomputable def ordinatePolynomial (W : WeierstrassCurve A) (x : A) : A[X] :=
  X ^ 2 + (C (W.a₁ * x + W.a₃) * X + C (-(x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆)))

theorem eval_ordinatePolynomial_eq_zero_iff (W : WeierstrassCurve A) (x y : A) :
    (ordinatePolynomial W x).eval y = 0 ↔ W.toAffine.Equation x y := by
  rw [WeierstrassCurve.Affine.equation_iff']
  simp only [ordinatePolynomial, eval_add, eval_mul, eval_pow, eval_X, eval_C]
  constructor <;> intro h <;> linear_combination h

theorem map_ordinatePolynomial {B : Type*} [CommRing B] (W : WeierstrassCurve A)
    (i : A →+* B) (x : A) :
    (ordinatePolynomial W x).map i = ordinatePolynomial (W.map i) (i x) := by
  simp [ordinatePolynomial]

private theorem ordinateLinearPart_degree_lt (b c : A) :
    (C b * X + C c).degree < 2 := degree_linear_le.trans_lt (by norm_num)

theorem monic_ordinatePolynomial (W : WeierstrassCurve A) (x : A) :
    (ordinatePolynomial W x).Monic :=
  monic_X_pow_add (ordinateLinearPart_degree_lt _ _)

theorem natDegree_ordinatePolynomial [Nontrivial A] (W : WeierstrassCurve A) (x : A) :
    (ordinatePolynomial W x).natDegree = 2 := by
  apply natDegree_eq_of_degree_eq_some
  unfold ordinatePolynomial
  have hpow : ((X : A[X]) ^ 2).degree = 2 := by simp
  rw [degree_add_eq_left_of_degree_lt]
  · simp [hpow]
  · rw [hpow]
    exact ordinateLinearPart_degree_lt _ _

/-- The branch polynomial gives the nonidentity two-torsion at even level.
The unit polynomial gives an empty branch at odd level. -/
noncomputable def branchPolynomial (W : WeierstrassCurve A) (n : ℕ) : A[X] :=
  if Even n then W.Ψ₂Sq else 1

/-- Adjoin an abscissa away from the two-torsion branch, then adjoin its ordinate. -/
noncomputable def unramifiedOrdinate (W : WeierstrassCurve A) (n : ℕ) :
    (AdjoinRoot (W.preΨ' n))[X] :=
  ordinatePolynomial (W.map (algebraMap A (AdjoinRoot (W.preΨ' n))))
    (AdjoinRoot.root (W.preΨ' n))

/-- Coordinate algebra of the disjoint union of the quadratic ordinate chart
and the even-level two-torsion chart. In the latter chart the equation
`2y + a₁x + a₃ = 0` determines the ordinate. -/
abbrev AffineTorsionAlgebra (W : WeierstrassCurve A) (n : ℕ) :=
  AdjoinRoot (unramifiedOrdinate W n) × AdjoinRoot (branchPolynomial W n)

private theorem isUnit_preΨ'_leadingCoeff (W : WeierstrassCurve A) {n : ℕ}
    (hn : IsUnit (n : A)) : IsUnit (W.preΨ' n).leadingCoeff := by
  cases subsingleton_or_nontrivial A with
  | inl _ =>
    exact (Subsingleton.elim (1 : A) (W.preΨ' n).leadingCoeff) ▸ isUnit_one
  | inr h =>
    rw [W.leadingCoeff_preΨ' hn.ne_zero]
    by_cases he : Even n
    · obtain ⟨m, rfl⟩ := he.two_dvd
      rw [ite_eq_left (even_two_mul m), Nat.mul_div_cancel_left _ two_pos]
      exact isUnit_of_mul_isUnit_right (show IsUnit ((2 : A) * m) from by simpa using hn)
    · simpa [he] using hn

private theorem isUnit_branch_leadingCoeff (W : WeierstrassCurve A) {n : ℕ}
    (hn : IsUnit (n : A)) : IsUnit (branchPolynomial W n).leadingCoeff := by
  cases subsingleton_or_nontrivial A with
  | inl _ =>
    exact (Subsingleton.elim (1 : A) (branchPolynomial W n).leadingCoeff) ▸ isUnit_one
  | inr h =>
    by_cases he : Even n
    · obtain ⟨m, rfl⟩ := he.two_dvd
      have h₂ : IsUnit (2 : A) :=
        isUnit_of_mul_isUnit_left (show IsUnit ((2 : A) * m) from by simpa using hn)
      have h₄ : IsUnit (4 : A) := by simpa only [show (2 : A) * 2 = 4 by ring] using h₂.mul h₂
      simpa [branchPolynomial, even_two_mul, W.leadingCoeff_Ψ₂Sq h₄.ne_zero] using h₄
    · simp [branchPolynomial, he]

private theorem xPolynomial_eq_mul (W : WeierstrassCurve A) (n : ℕ) :
    xPolynomial W n = W.preΨ' n * branchPolynomial W n := by
  by_cases he : Even n <;> simp [xPolynomial, branchPolynomial, he]

private theorem map_branchPolynomial {B : Type*} [CommRing B] (W : WeierstrassCurve A)
    (i : A →+* B) (n : ℕ) :
    (branchPolynomial W n).map i = branchPolynomial (W.map i) n := by
  by_cases he : Even n <;> simp [branchPolynomial, he, W.map_Ψ₂Sq]

private theorem ordinate_derivative_ne_zero_of_preΨ {K : Type*} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) {x y : K}
    (hx : (W.preΨ' n).eval x = 0) (hy : W.toAffine.Equation x y) :
    (ordinatePolynomial W x).derivative.eval y ≠ 0 := by
  classical
  intro hd
  have hyneg : y = W.toAffine.negY x y := by
    simp only [ordinatePolynomial, derivative_add, derivative_C_mul_X, derivative_C,
      derivative_X_pow, Nat.cast_two, show 2 - 1 = 1 by decide, pow_one,
      eval_add, eval_mul, eval_X, eval_C, add_zero] at hd
    rw [WeierstrassCurve.Affine.negY]
    linear_combination hd
  rcases n.even_or_odd' with ⟨m, rfl | rfl⟩
  · have hc : W.Ψ₂Sq.eval x = 0 := (eval_Ψ₂Sq_eq_zero_iff W hy).2 hyneg
    have hs := separable_xPolynomial W hn
    rw [xPolynomial, ite_eq_left (even_two_mul m)] at hs
    exact hs.eval₂_derivative_ne_zero (RingHom.id K) (x := x)
      (by simp [hx]) (by simp [derivative_mul, hx, hc])
  · have hns := W.toAffine.equation_iff_nonsingular.mp hy
    let P : W.toAffine.Point := Point.some x y hns
    have h₂ : (2 : ℕ) • P = 0 := by
      rw [two_nsmul]
      exact Point.add_self_of_Y_eq hyneg
    have hodd : (2 * m + 1) • P = 0 := (nsmul_some_eq_zero_iff W _ hns).2
      (by simpa [xPolynomial, m.not_even_two_mul_add_one] using hx)
    have hp : P = 0 := by
      rw [add_nsmul, mul_nsmul, h₂, smul_zero, zero_add, one_nsmul] at hodd
      exact hodd
    exact Point.some_ne_zero _ hp

private theorem unit_derivative_unramifiedOrdinate (W : WeierstrassCurve A) [W.IsElliptic]
    {n : ℕ} (hn : IsUnit (n : A)) :
    IsUnit (AdjoinRoot.mk (unramifiedOrdinate W n) (unramifiedOrdinate W n).derivative) := by
  apply isUnit_mk_of_no_common_root
  intro K _ i y hy
  let P := W.preΨ' n
  let r := AdjoinRoot.root P
  let j := i.comp (algebraMap A (AdjoinRoot P))
  have hr : ((W.map j).preΨ' n).eval (i r) = 0 := by
    rw [W.map_preΨ', eval_map]
    rw [← hom_eval₂]
    change i (P.eval₂ (algebraMap A (AdjoinRoot P)) (AdjoinRoot.root P)) = 0
    rw [AdjoinRoot.algebraMap_eq, AdjoinRoot.eval₂_root, map_zero]
  have hmap : (unramifiedOrdinate W n).map i = ordinatePolynomial (W.map j) (i r) := by
    rw [unramifiedOrdinate, map_ordinatePolynomial, WeierstrassCurve.map_map]
  rw [hmap] at hy
  rw [← derivative_map, hmap]
  exact ordinate_derivative_ne_zero_of_preΨ (W.map j) (by simpa using (hn.map j).ne_zero)
    hr ((eval_ordinatePolynomial_eq_zero_iff _ _ _).mp hy)

private theorem etale_prod {B C : Type v} [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] [Algebra.Etale A B] [Algebra.Etale A C] :
    Algebra.Etale A (B × C) := by
  let D : Bool → Type _ := fun b => if b then B else C
  let instR (b : Bool) : CommRing (D b) := by cases b <;> dsimp [D] <;> infer_instance
  let instA (b : Bool) : Algebra A (D b) := by cases b <;> dsimp [D, instR] <;> infer_instance
  let instE (b : Bool) : Algebra.Etale A (D b) := by
    cases b <;> dsimp [D, instR, instA] <;> infer_instance
  let fromPair (z : B × C) (b : Bool) : D b := by
    cases b
    · exact z.2
    · exact z.1
  let e : (Π b, D b) ≃ₐ[A] (B × C) :=
    { toFun := fun x => (x true, x false)
      invFun := fromPair
      left_inv := fun x => funext (fun b => by cases b <;> rfl)
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  exact Algebra.Etale.of_equiv e

/-- The affine nonidentity torsion coordinate algebra is finite free and étale. -/
theorem affineTorsionAlgebra_finite_etale (W : WeierstrassCurve A) [W.IsElliptic]
    {n : ℕ} (hn : IsUnit (n : A)) :
    Module.Finite A (AffineTorsionAlgebra W n) ∧ Module.Free A (AffineTorsionAlgebra W n) ∧
      Algebra.Etale A (AffineTorsionAlgebra W n) := by
  have hsep (K : Type u) [Field K] (i : A →+* K) :
      ((W.map i).preΨ' n * branchPolynomial (W.map i) n).Separable := by
    rw [← xPolynomial_eq_mul]
    exact separable_xPolynomial (W.map i) (by simpa using (hn.map i).ne_zero)
  obtain ⟨_, hpf, hpr, hpe⟩ := monogenic_of_separable_specializations _
    (isUnit_preΨ'_leadingCoeff W hn) fun K _ i => by
      rw [← W.map_preΨ']
      exact (hsep K i).of_dvd (dvd_mul_right _ _)
  obtain ⟨_, hbf, hbr, hbe⟩ := monogenic_of_separable_specializations _
    (isUnit_branch_leadingCoeff W hn) fun K _ i => by
      rw [map_branchPolynomial]
      exact (hsep K i).of_dvd (dvd_mul_left _ _)
  let B := AdjoinRoot (W.preΨ' n)
  let C := AdjoinRoot (unramifiedOrdinate W n)
  have hm : (unramifiedOrdinate W n).Monic := monic_ordinatePolynomial _ _
  have : Module.Finite B C := hm.finite_adjoinRoot
  have : Module.Free B C := hm.free_adjoinRoot
  have : Algebra.Etale B C :=
    etale_adjoinRoot_of_unit_derivative hm (unit_derivative_unramifiedOrdinate W hn)
  have : Module.Finite A C := Module.Finite.trans B C
  have : Module.Free A C := Module.Free.trans (S := B)
  have : Algebra.Etale A C := .comp A B C
  exact ⟨inferInstance, inferInstance, etale_prod⟩

/-- Over an algebraically closed field, every root of the abscissa polynomial
is the abscissa of a nonidentity torsion point. -/
theorem exists_torsion_ordinate {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} {x : K}
    (hx : (xPolynomial W n).eval x = 0) :
    ∃ (y : K) (h : W.toAffine.Nonsingular x y),
      n • (Point.some x y h : W.toAffine.Point) = 0 := by
  classical
  have hd : (ordinatePolynomial W x).degree ≠ 0 := by
    rw [degree_eq_natDegree (monic_ordinatePolynomial W x).ne_zero, natDegree_ordinatePolynomial]
    norm_num
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root _ hd
  have h := W.toAffine.equation_iff_nonsingular.mp
    ((eval_ordinatePolynomial_eq_zero_iff W x y).mp hy)
  exact ⟨y, h, (nsmul_some_eq_zero_iff W n h).2 hx⟩

private theorem weighted_degree_torsion_factors (W : WeierstrassCurve A) [Nontrivial A]
    {n : ℕ} (hn : IsUnit (n : A)) :
    (W.preΨ' n).natDegree * 2 + (branchPolynomial W n).natDegree = n ^ 2 - 1 := by
  rw [W.natDegree_preΨ' hn.ne_zero]
  rcases n.even_or_odd' with ⟨m, rfl | rfl⟩
  · have h₂m : IsUnit ((2 : A) * (m : A)) := by simpa using hn
    have h₂ := isUnit_of_mul_isUnit_left h₂m
    have h₄ : IsUnit (4 : A) := by simpa only [show (2 : A) * 2 = 4 by ring] using h₂.mul h₂
    have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at h₂m)
    simp only [branchPolynomial, ite_eq_left (even_two_mul m), W.natDegree_Ψ₂Sq h₄.ne_zero]
    have hsq : (2 * m) ^ 2 = 4 * (m * m) := by ring
    have hlarge : 0 < m * m := Nat.mul_pos hm hm
    rw [hsq]
    omega
  · simp only [branchPolynomial, ite_eq_right m.not_even_two_mul_add_one, natDegree_one, add_zero]
    have hsq : (2 * m + 1) ^ 2 = 4 * (m * m + m) + 1 := by ring
    rw [hsq]
    omega

/-- The affine torsion algebra has rank one less than the full torsion. -/
theorem finrank_affineTorsionAlgebra (W : WeierstrassCurve A) [Nontrivial A]
    {n : ℕ} (hn : IsUnit (n : A)) :
    Module.finrank A (AffineTorsionAlgebra W n) = n ^ 2 - 1 := by
  let f := W.preΨ' n
  let q := unramifiedOrdinate W n
  let bf := basisAdjoinRoot f (isUnit_preΨ'_leadingCoeff W hn)
  let bq := (AdjoinRoot.powerBasis' (monic_ordinatePolynomial
    (W.map (algebraMap A (AdjoinRoot f))) (AdjoinRoot.root f))).basis
  let bg := basisAdjoinRoot (branchPolynomial W n) (isUnit_branch_leadingCoeff W hn)
  have hq : f.natDegree * q.natDegree = f.natDegree * 2 := by
    cases subsingleton_or_nontrivial (AdjoinRoot f) with
    | inr _ => rw [show q.natDegree = 2 from natDegree_ordinatePolynomial _ _]
    | inl _ =>
      have h := Module.finrank_eq_card_basis bf
      rw [Fintype.card_fin, Module.finrank_zero_of_subsingleton] at h
      rw [← h, zero_mul, zero_mul]
  have h := Module.finrank_eq_card_basis ((bf.smulTower bq).prod bg)
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at h
  change Module.finrank A (AffineTorsionAlgebra W n) =
    f.natDegree * q.natDegree + (branchPolynomial W n).natDegree at h
  rw [h, hq]
  exact weighted_degree_torsion_factors W hn

#print axioms eval_ordinatePolynomial_eq_zero_iff
#print axioms map_ordinatePolynomial
#print axioms ordinateLinearPart_degree_lt
#print axioms monic_ordinatePolynomial
#print axioms natDegree_ordinatePolynomial
#print axioms isUnit_preΨ'_leadingCoeff
#print axioms isUnit_branch_leadingCoeff
#print axioms xPolynomial_eq_mul
#print axioms map_branchPolynomial
#print axioms ordinate_derivative_ne_zero_of_preΨ
#print axioms unit_derivative_unramifiedOrdinate
#print axioms etale_prod
#print axioms affineTorsionAlgebra_finite_etale
#print axioms exists_torsion_ordinate
#print axioms weighted_degree_torsion_factors
#print axioms finrank_affineTorsionAlgebra

end WeierstrassCurve.ModelTorsion
