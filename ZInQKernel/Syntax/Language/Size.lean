import ZInQKernel.Syntax.Language.Formula

/-!
# Coefficient bounds

The ℓ¹ norm `l1 f` of an integer polynomial is the sum of the absolute values of its
coefficients. It bounds every coefficient, is subadditive and submultiplicative, and a
substitution `bind₁ g P` has norm at most `l1 P · B ^ deg P` when every substituted polynomial
has norm at most `B ≥ 1`. Together with the degree bounds of `Basic` and `Formula` these give
compositional size bounds for calls, sums of squares and products.
-/

namespace ZInQ.Syntax

open MvPolynomial

variable {σ τ : Type*}

/-- The sum of the absolute values of the coefficients. -/
def l1 (f : MvPolynomial σ ℤ) : ℕ := ∑ d ∈ f.support, (f.coeff d).natAbs

theorem l1_eq_sum_of_subset {f : MvPolynomial σ ℤ} {S : Finset (σ →₀ ℕ)} (h : f.support ⊆ S) :
    l1 f = ∑ d ∈ S, (f.coeff d).natAbs :=
  Finset.sum_subset h fun d _ hd => by rw [notMem_support_iff.1 hd, Int.natAbs_zero]

/-- The ℓ¹ norm bounds every coefficient. -/
theorem natAbs_coeff_le_l1 (f : MvPolynomial σ ℤ) (d : σ →₀ ℕ) : (f.coeff d).natAbs ≤ l1 f := by
  by_cases hd : d ∈ f.support
  · exact Finset.single_le_sum (f := fun d => (f.coeff d).natAbs) (fun _ _ => Nat.zero_le _) hd
  · rw [notMem_support_iff.1 hd, Int.natAbs_zero]
    exact Nat.zero_le _

@[simp] theorem l1_zero : l1 (0 : MvPolynomial σ ℤ) = 0 := by simp [l1]

theorem l1_monomial (d : σ →₀ ℕ) (c : ℤ) : l1 (monomial d c) = c.natAbs := by
  classical
  by_cases hc : c = 0
  · subst hc; simp
  · rw [l1, support_monomial, ite_eq_right hc, Finset.sum_singleton, coeff_monomial, ite_eq_left rfl]

theorem l1_C (c : ℤ) : l1 (C c : MvPolynomial σ ℤ) = c.natAbs := l1_monomial 0 c

theorem l1_one : l1 (1 : MvPolynomial σ ℤ) = 1 := by
  rw [← C_1, l1_C]; rfl

theorem l1_X (i : σ) : l1 (X i : MvPolynomial σ ℤ) = 1 := by
  rw [X, l1_monomial]; rfl

theorem l1_neg (f : MvPolynomial σ ℤ) : l1 (-f) = l1 f := by
  simp [l1, support_neg, Int.natAbs_neg]

theorem l1_add_le (f g : MvPolynomial σ ℤ) : l1 (f + g) ≤ l1 f + l1 g := by
  classical
  rw [l1_eq_sum_of_subset support_add, l1_eq_sum_of_subset (f := f) Finset.subset_union_left,
    l1_eq_sum_of_subset (f := g) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [show (f + g).coeff d = f.coeff d + g.coeff d by simp]
  exact Int.natAbs_add_le _ _

theorem l1_sub_le (f g : MvPolynomial σ ℤ) : l1 (f - g) ≤ l1 f + l1 g := by
  rw [sub_eq_add_neg, ← l1_neg g]
  exact l1_add_le f (-g)

theorem l1_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    l1 (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (l1_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem l1_mul_le (f g : MvPolynomial σ ℤ) : l1 (f * g) ≤ l1 f * l1 g := by
  conv_lhs => rw [f.as_sum, g.as_sum]
  rw [Finset.sum_mul_sum]
  refine (l1_finset_sum_le _ _).trans ?_
  rw [l1, l1, Finset.sum_mul_sum]
  refine Finset.sum_le_sum fun a _ => (l1_finset_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [monomial_mul_monomial, l1_monomial, Int.natAbs_mul]

theorem l1_pow_le (f : MvPolynomial σ ℤ) (n : ℕ) : l1 (f ^ n) ≤ l1 f ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, l1_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (l1_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

theorem l1_finset_prod_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    l1 (∏ i ∈ s, f i) ≤ ∏ i ∈ s, l1 (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [l1_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (l1_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

theorem l1_list_sum_le (l : List (MvPolynomial σ ℤ)) : l1 l.sum ≤ (l.map l1).sum := by
  induction l with
  | nil => simp
  | cons f l ih =>
    rw [List.sum_cons, List.map_cons, List.sum_cons]
    exact (l1_add_le _ _).trans (Nat.add_le_add_left ih _)

theorem l1_list_prod_le (l : List (MvPolynomial σ ℤ)) : l1 l.prod ≤ (l.map l1).prod := by
  induction l with
  | nil => simp [l1_one]
  | cons f l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons]
    exact (l1_mul_le _ _).trans (Nat.mul_le_mul_left _ ih)

/-- Norm of a sum of squares. -/
theorem l1_sum_sq_le (l : List (MvPolynomial σ ℤ)) :
    l1 (l.map (· ^ 2)).sum ≤ (l.map fun f => l1 f ^ 2).sum := by
  refine (l1_list_sum_le _).trans ?_
  rw [List.map_map]
  exact List.sum_le_sum fun f _ => l1_pow_le f 2

/-- **Substitution.** If every substituted polynomial has norm at most `B ≥ 1`, then
`l1 (bind₁ g P) ≤ l1 P · B ^ deg P`. -/
theorem l1_bind₁_le (g : σ → MvPolynomial τ ℤ) (P : MvPolynomial σ ℤ) {B : ℕ} (hB : 1 ≤ B)
    (h : ∀ i ∈ P.vars, l1 (g i) ≤ B) : l1 (bind₁ g P) ≤ l1 P * B ^ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (l1_finset_sum_le _ _).trans ?_
  rw [l1, Finset.sum_mul]
  refine Finset.sum_le_sum fun d hd => ?_
  rw [bind₁_monomial]
  refine (l1_mul_le _ _).trans ?_
  rw [l1_C]
  refine Nat.mul_le_mul_left _ ?_
  refine (l1_finset_prod_le _ _).trans ?_
  calc ∏ i ∈ d.support, l1 (g i ^ d i) ≤ ∏ i ∈ d.support, B ^ d i := by
        refine Finset.prod_le_prod fun i hi => ?_
        refine (l1_pow_le _ _).trans (Nat.pow_le_pow_left ?_ _)
        exact h i ((mem_vars_iff_mem_support i).2 ⟨d, hd, hi⟩)
    _ = B ^ (∑ i ∈ d.support, d i) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ B ^ P.totalDegree := Nat.pow_le_pow_right hB (le_totalDegree hd)

/-- Norm of a call: `l1 (P[g; w]) ≤ l1 P · B ^ deg P` when every parameter polynomial has norm
at most `B ≥ 1`. -/
theorem l1_callPoly_le (P : Poly) (p w : ℕ) (g : Fin p → Poly) {B : ℕ} (hB : 1 ≤ B)
    (hg : ∀ k, l1 (g k) ≤ B) : l1 (callPoly P p w g) ≤ l1 P * B ^ P.totalDegree := by
  refine l1_bind₁_le _ _ hB fun i _ => ?_
  unfold callSubst
  split_ifs
  · exact hg _
  · rw [l1_X]; exact hB

/-- Renaming along an injective map preserves the norm. -/
theorem l1_rename_of_injective {f : σ → τ} (hf : Function.Injective f) (Q : MvPolynomial σ ℤ) :
    l1 (rename f Q) = l1 Q := by
  classical
  rw [l1, support_rename_of_injective hf, Finset.sum_image]
  · exact Finset.sum_congr rfl fun d _ => by rw [coeff_rename_mapDomain f hf]
  · intro a _ b _ hab
    exact Finsupp.mapDomain_injective hf hab

namespace Formula

/-- A norm bound computed from the formula: `l1 a + l1 b` for `a ≐ b`, the norm of an atom or
call polynomial, the sum of the squared bounds of the conjuncts and the product of the bounds
of the disjuncts. -/
noncomputable def normBound : Formula → ℕ
  | .eq a b => l1 a + l1 b
  | .atom f => l1 f
  | .call τ g w => l1 (τ.call g w)
  | .and fs => (fs.map fun φ => φ.normBound ^ 2).sum
  | .or fs => (fs.map fun φ => φ.normBound).prod

/-- The norm of a compiled formula is at most `Formula.normBound`. -/
theorem l1_compile_le (φ : Formula) : l1 φ.compile ≤ φ.normBound := by
  induction φ using Formula.induct' with
  | eq a b => simpa [normBound] using l1_sub_le a b
  | atom f => simp [normBound]
  | call τ g w => simp [normBound]
  | and fs ih =>
    rw [compile_and, normBound]
    refine (l1_list_sum_le _).trans ?_
    rw [List.map_map]
    exact List.sum_le_sum fun φ hφ =>
      (l1_pow_le _ 2).trans (Nat.pow_le_pow_left (ih φ hφ) 2)
  | or fs ih =>
    rw [compile_or, normBound]
    refine (l1_list_prod_le _).trans ?_
    rw [List.map_map]
    exact List.prod_le_prod fun φ hφ => ih φ hφ

end Formula

end ZInQ.Syntax
