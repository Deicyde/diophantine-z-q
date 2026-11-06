import ZInQKernel.Model.DivisionPolynomials.Jacobian

/-!
# The Jacobian identities at every point

The identities `dblXYZ (jac n) = 8 • jac (2n)` and `addXYZ (jac (n+1)) (jac n) = (-8) • jac (2n+1)`
hold at every point of `y² = x³ + Ax` over a field of characteristic zero. They are first proved
at the generic point of the curve, in the function field `Frac K[W]`, where no `ψ_n` (`n ≠ 0`)
vanishes because `f_n` has leading coefficient `n` or `n/2` (Mathlib's `preΨ'_ne_zero`). They are
then identities in the coordinate ring `K[W]`, and evaluation at a point gives them there.
-/

namespace ZInQ.DivisionPolynomials

open WeierstrassCurve WeierstrassCurve.Jacobian Polynomial
open scoped Polynomial.Bivariate
open ZInQ.Syntax (WA divD0 divF3 divF4 normDiv normDiv_eq_preΨ')

lemma map_smul_fin3 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : R)
    (P : Fin 3 → R) : f ∘ (u • P) = f u • (f ∘ P) := by
  ext i
  fin_cases i <;> simp [smul_fin3]

variable {K : Type*} [Field K] (A : K)

/-- The embedding `K[x] → K[W]`. -/
noncomputable def φC : K[X] →+* (WA A).toAffine.CoordinateRing :=
  algebraMap K[X] (WA A).toAffine.CoordinateRing

lemma φC_apply (p : K[X]) : φC A p = Affine.CoordinateRing.mk (WA A).toAffine (C p) := rfl

lemma φC_injective : Function.Injective (φC A) :=
  FaithfulSMul.algebraMap_injective K[X] (WA A).toAffine.CoordinateRing

/-- The generic abscissa `x ∈ K[W]`. -/
noncomputable def gx : (WA A).toAffine.CoordinateRing := φC A X

/-- The generic ordinate `y ∈ K[W]`. -/
noncomputable def gy : (WA A).toAffine.CoordinateRing := Affine.CoordinateRing.mk (WA A).toAffine Y

/-- The coefficient `A ∈ K[W]`. -/
noncomputable def gA : (WA A).toAffine.CoordinateRing := φC A (C A)

lemma φC_X : φC A X = gx A := rfl
lemma φC_CA : φC A (C A) = gA A := rfl

lemma WA_polynomial : (WA A).toAffine.polynomial = Y ^ 2 - C (X ^ 3 + C A * X) := by
  simp [Affine.polynomial, WA]

lemma g_eq : gy A ^ 2 = gx A ^ 3 + gA A * gx A := by
  have h : AdjoinRoot.mk (WA A).toAffine.polynomial (Y ^ 2 - C (X ^ 3 + C A * X)) = 0 := by
    rw [← WA_polynomial]; exact AdjoinRoot.mk_self
  simp only [map_sub, map_pow] at h
  have e : AdjoinRoot.mk (WA A).toAffine.polynomial (C (X ^ 3 + C A * X)) =
      gx A ^ 3 + gA A * gx A := by
    rw [← φC_apply]; simp [φC_X, φC_CA]
  rw [e] at h
  simp only [gy]
  linear_combination h

lemma gy_ne_zero : gy A ≠ 0 := by
  simpa [Affine.CoordinateRing.YClass, gy] using
    Affine.CoordinateRing.YClass_ne_zero (W' := (WA A).toAffine) 0

lemma CR_two_ne_zero [CharZero K] : (2 : (WA A).toAffine.CoordinateRing) ≠ 0 := by
  rw [← map_ofNat (φC A) 2]
  exact (map_ne_zero_iff _ (φC_injective A)).mpr two_ne_zero

lemma w_generic (n : ℕ) : w (gA A) (gx A) (gy A) n =
    φC A (normDiv A n) * if Even n then 2 * gy A else 1 := by
  have hb : (2 * gy A) ^ 4 = φC A (divD0 A) := by
    simp only [divD0, map_mul, map_pow, map_add, map_ofNat, φC_X, φC_CA]
    linear_combination (16 * (gy A ^ 2 + (gx A ^ 3 + gA A * gx A))) * g_eq A
  rw [w, normEDS_ofNat, hb, normDiv, map_preNormEDS']
  congr 3
  · simp [divF3, φC_X, φC_CA, map_ofNat]
  · simp [divF4, φC_X, φC_CA, map_ofNat]

variable [CharZero K]

lemma w_generic_ne_zero (n : ℤ) (hn : n ≠ 0) : w (gA A) (gx A) (gy A) n ≠ 0 := by
  have key : ∀ k : ℕ, k ≠ 0 → w (gA A) (gx A) (gy A) k ≠ 0 := by
    intro k hk
    rw [w_generic]
    refine mul_ne_zero ?_ ?_
    · rw [map_ne_zero_iff _ (φC_injective A), normDiv_eq_preΨ']
      exact preΨ'_ne_zero _ (by exact_mod_cast hk)
    · split_ifs
      · exact mul_ne_zero (CR_two_ne_zero A) (gy_ne_zero A)
      · exact one_ne_zero
  rcases Int.natAbs_eq n with h | h
  · rw [h]; exact key _ (by omega)
  · rw [h, w_neg, neg_ne_zero]; exact key _ (by omega)

/-- Pull an identity of Jacobian triples back along an injective ring homomorphism. -/
lemma eq_of_map_eq {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) {P Q : Fin 3 → R} (h : f ∘ P = f ∘ Q) : P = Q :=
  funext fun i => hf (congrFun h i)

omit [CharZero K] in
lemma evalEval_gx {x y : K} (h : (WA A).toAffine.Equation x y) :
    AdjoinRoot.evalEval h (gx A) = x := by
  have := AdjoinRoot.evalEval_mk h (C X)
  rw [evalEval_C, eval_X] at this
  exact this

omit [CharZero K] in
lemma evalEval_gy {x y : K} (h : (WA A).toAffine.Equation x y) :
    AdjoinRoot.evalEval h (gy A) = y := by
  exact (AdjoinRoot.evalEval_mk h Y).trans (by simp)

omit [CharZero K] in
lemma evalEval_gA {x y : K} (h : (WA A).toAffine.Equation x y) :
    AdjoinRoot.evalEval h (gA A) = A := by
  exact (AdjoinRoot.evalEval_mk h (C (C A))).trans (by simp)

/-- The identities in the coordinate ring. -/
theorem jac_identities_generic (n : ℕ) (hn : 1 ≤ n) :
    (WA (gA A)).toJacobian.dblXYZ (jac (gA A) (gx A) (gy A) n) =
        (8 : (WA A).toAffine.CoordinateRing) • jac (gA A) (gx A) (gy A) (2 * n) ∧
      (WA (gA A)).toJacobian.addXYZ (jac (gA A) (gx A) (gy A) (n + 1))
          (jac (gA A) (gx A) (gy A) n) =
        (-8 : (WA A).toAffine.CoordinateRing) • jac (gA A) (gx A) (gy A) (2 * n + 1) := by
  classical
  let ι := algebraMap (WA A).toAffine.CoordinateRing (WA A).toAffine.FunctionField
  have hι : Function.Injective ι := IsFractionRing.injective _ _
  have h2L : (2 : (WA A).toAffine.FunctionField) ≠ 0 := by
    rw [← map_ofNat ι 2]; exact (map_ne_zero_iff _ hι).mpr (CR_two_ne_zero A)
  have hgy : ι (gy A) ≠ 0 := (map_ne_zero_iff _ hι).mpr (gy_ne_zero A)
  have hns : (WA (ι (gA A))).toAffine.Nonsingular (ι (gx A)) (ι (gy A)) := by
    rw [Affine.nonsingular_iff', WA_equation_iff]
    refine ⟨?_, Or.inr ?_⟩
    · rw [← map_pow, g_eq]; simp
    · rw [show (WA (ι (gA A))).a₁ = 0 from rfl, show (WA (ι (gA A))).a₃ = 0 from rfl, zero_mul,
        add_zero, add_zero]
      exact mul_ne_zero h2L hgy
  have hwL : ∀ n : ℤ, n ≠ 0 → w (ι (gA A)) (ι (gx A)) (ι (gy A)) n ≠ 0 := by
    intro n hn; rw [← map_w]; exact (map_ne_zero_iff _ hι).mpr (w_generic_ne_zero A n hn)
  obtain ⟨hD, hS⟩ := jac_identities_of_ne_zero h2L hns hwL n hn
  simp only [← map_jac, ← WA_map] at hD hS
  constructor
  · refine eq_of_map_eq hι ?_
    rw [map_smul_fin3, map_ofNat, ← map_dblXYZ]
    exact hD
  · refine eq_of_map_eq hι ?_
    rw [map_smul_fin3, map_neg, map_ofNat, ← map_addXYZ]
    exact hS

/-- **The doubling and addition identities at every point** of `y² = x³ + Ax` over a field of
characteristic zero. -/
theorem jac_identities {x y : K} (h : (WA A).toAffine.Equation x y) (n : ℕ) (hn : 1 ≤ n) :
    (WA A).toJacobian.dblXYZ (jac A x y n) = (8 : K) • jac A x y (2 * n) ∧
      (WA A).toJacobian.addXYZ (jac A x y (n + 1)) (jac A x y n) =
        (-8 : K) • jac A x y (2 * n + 1) := by
  obtain ⟨hD, hS⟩ := jac_identities_generic A n hn
  let e := AdjoinRoot.evalEval h
  have hD' := congrArg (e ∘ ·) hD
  have hS' := congrArg (e ∘ ·) hS
  simp only [← map_dblXYZ, ← map_addXYZ, map_smul_fin3, map_jac, WA_map, map_ofNat, map_neg] at hD' hS'
  simp only [e, evalEval_gx, evalEval_gy, evalEval_gA] at hD' hS'
  exact ⟨hD', hS'⟩

end ZInQ.DivisionPolynomials
