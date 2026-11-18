import ZInQKernel.Contrib.OneProof.RC.Symbols.Core

/-!
# Lane RC2: the action of difference polynomials on Boolean functions of flip sets

The action `act` of `Core` (a monomial `X^m` acts by the iterated finite difference over
`supp m` when `m` is squarefree, else by `0`) is an algebra action: it is additive and
multiplicative in the polynomial and `1` acts as the identity (tex 2219, 10635–10655, where
products of network operators act by composition). We also record the action of a single
variable (the difference `Δ_e`), of constants and monomials, and linearity in the function.
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset

open Classical in
/-- The operator of one monomial: iterated difference over `supp m` if `m` is squarefree,
else `0`. -/
noncomputable def actT (m : Sym2 ℕ →₀ ℕ) (f : Finset (Sym2 ℕ) → ZMod 2)
    (U : Finset (Sym2 ℕ)) : ZMod 2 :=
  if ∀ e, m e ≤ 1 then ∑ W ∈ m.support.powerset, f (symmDiff U W) else 0


/-- `act` as a sum over any finite set of monomials containing the support (tex 2219, 10635–10655). PROVED. -/
theorem act_eq_sum (p : MvPolynomial (Sym2 ℕ) (ZMod 2)) (f : Finset (Sym2 ℕ) → ZMod 2)
    (U : Finset (Sym2 ℕ)) {s : Finset (Sym2 ℕ →₀ ℕ)} (hs : p.support ⊆ s) :
    act p f U = ∑ m ∈ s, p.coeff m * actT m f U := by
  unfold act actT
  apply Finset.sum_subset hs
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]

/-- Additivity of the action in the polynomial (tex 2219). PROVED. -/
theorem act_add (p q : MvPolynomial (Sym2 ℕ) (ZMod 2)) (f : Finset (Sym2 ℕ) → ZMod 2) :
    act (p + q) f = fun U => act p f U + act q f U := by
  funext U
  have h1 : (p + q).support ⊆ (p + q).support ∪ p.support ∪ q.support := by
    intro m hm; simp [hm]
  have h2 : p.support ⊆ (p + q).support ∪ p.support ∪ q.support := by
    intro m hm; simp [hm]
  have h3 : q.support ⊆ (p + q).support ∪ p.support ∪ q.support := by
    intro m hm; simp [hm]
  rw [act_eq_sum _ f U h1, act_eq_sum _ f U h2, act_eq_sum _ f U h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

/-- The zero polynomial acts by zero (tex 2219, 10635–10655). PROVED. -/
theorem act_zero (f : Finset (Sym2 ℕ) → ZMod 2) : act 0 f = fun _ => 0 := by
  funext U; simp [act]

/-- A monomial acts by its coefficient times the monomial operator (tex 2219, 10635–10655). PROVED. -/
theorem act_monomial (u : Sym2 ℕ →₀ ℕ) (a : ZMod 2) (f : Finset (Sym2 ℕ) → ZMod 2)
    (U : Finset (Sym2 ℕ)) : act (MvPolynomial.monomial u a) f U = a * actT u f U := by
  rw [act_eq_sum _ f U (MvPolynomial.support_monomial_subset), Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

/-- Linearity of the monomial operator in the function (sum) (tex 2219, 10635–10655). PROVED. -/
theorem actT_add_fun (m : Sym2 ℕ →₀ ℕ) (f g : Finset (Sym2 ℕ) → ZMod 2) (U : Finset (Sym2 ℕ)) :
    actT m (fun V => f V + g V) U = actT m f U + actT m g U := by
  unfold actT
  split_ifs
  · rw [Finset.sum_add_distrib]
  · simp

/-- Linearity of the monomial operator in the function (scalar) (tex 2219, 10635–10655). PROVED. -/
theorem actT_smul_fun (m : Sym2 ℕ →₀ ℕ) (c : ZMod 2) (f : Finset (Sym2 ℕ) → ZMod 2)
    (U : Finset (Sym2 ℕ)) : actT m (fun V => c * f V) U = c * actT m f U := by
  unfold actT
  split_ifs
  · rw [Finset.mul_sum]
  · simp

/-- Linearity of the action in the function (sum) (tex 2219, 10635–10655). PROVED. -/
theorem act_add_fun (p : MvPolynomial (Sym2 ℕ) (ZMod 2)) (f g : Finset (Sym2 ℕ) → ZMod 2)
    (U : Finset (Sym2 ℕ)) : act p (fun V => f V + g V) U = act p f U + act p g U := by
  rw [act_eq_sum p _ U subset_rfl, act_eq_sum p f U subset_rfl, act_eq_sum p g U subset_rfl,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [actT_add_fun, mul_add]

/-- Linearity of the action in the function (scalar) (tex 2219, 10635–10655). PROVED. -/
theorem act_smul_fun (p : MvPolynomial (Sym2 ℕ) (ZMod 2)) (c : ZMod 2)
    (f : Finset (Sym2 ℕ) → ZMod 2) (U : Finset (Sym2 ℕ)) :
    act p (fun V => c * f V) U = c * act p f U := by
  rw [act_eq_sum p _ U subset_rfl, act_eq_sum p f U subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [actT_smul_fun]; ring

/-- The zero monomial acts as the identity (tex 2219, 10635–10655). PROVED. -/
theorem actT_zero (f : Finset (Sym2 ℕ) → ZMod 2) : actT 0 f = f := by
  funext U
  have h : symmDiff U (∅ : Finset (Sym2 ℕ)) = U := symmDiff_bot U
  simp [actT, h]

/-- A monomial with an exponent at least two acts by zero (tex 2219, 10635–10655). PROVED. -/
theorem actT_eq_zero_of_two_le {m : Sym2 ℕ →₀ ℕ} {e : Sym2 ℕ} (he : 2 ≤ m e)
    (f : Finset (Sym2 ℕ) → ZMod 2) (U : Finset (Sym2 ℕ)) : actT m f U = 0 := by
  unfold actT
  rw [if_neg]
  intro h
  have := h e
  omega

/-- Multiplying a monomial by one more variable applies one more difference
(`Δ_e² = 0` when the variable is already present) (tex 2219, 10635–10655). PROVED. -/
theorem actT_single_add (e : Sym2 ℕ) (b : Sym2 ℕ →₀ ℕ) (g : Finset (Sym2 ℕ) → ZMod 2)
    (U : Finset (Sym2 ℕ)) :
    actT (Finsupp.single e 1 + b) g U = actT b g U + actT b g (symmDiff U {e}) := by
  by_cases hb : ∀ x, b x ≤ 1
  · by_cases he : e ∈ b.support
    · have h2 : 2 ≤ ((Finsupp.single e 1 + b : Sym2 ℕ →₀ ℕ)) e := by
        rw [Finsupp.mem_support_iff] at he
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]
        omega
      rw [actT_eq_zero_of_two_le h2]
      unfold actT
      simp only [if_pos hb]
      have hsum : ∑ W ∈ b.support.powerset, g (symmDiff (symmDiff U {e}) W) =
          ∑ W ∈ b.support.powerset, g (symmDiff U W) := by
        refine Finset.sum_nbij' (fun W => symmDiff {e} W) (fun W => symmDiff {e} W)
          ?_ ?_ ?_ ?_ ?_
        · intro W hW
          rw [Finset.mem_powerset] at hW ⊢
          intro x hx
          rw [Finset.mem_symmDiff] at hx
          rcases hx with ⟨hx, _⟩ | ⟨hx, _⟩
          · rw [Finset.mem_singleton] at hx; rw [hx]; exact he
          · exact hW hx
        · intro W hW
          rw [Finset.mem_powerset] at hW ⊢
          intro x hx
          rw [Finset.mem_symmDiff] at hx
          rcases hx with ⟨hx, _⟩ | ⟨hx, _⟩
          · rw [Finset.mem_singleton] at hx; rw [hx]; exact he
          · exact hW hx
        · intro W _
          exact symmDiff_symmDiff_cancel_left _ _
        · intro W _
          exact symmDiff_symmDiff_cancel_left _ _
        · intro W _
          rw [symmDiff_assoc]
      rw [hsum, zmod2_add_self]
    · have h1 : ∀ x, ((Finsupp.single e 1 + b : Sym2 ℕ →₀ ℕ)) x ≤ 1 := by
        intro x
        rw [Finsupp.mem_support_iff, not_not] at he
        simp only [Finsupp.add_apply, Finsupp.single_apply]
        split_ifs with hx
        · subst hx; omega
        · have := hb x; omega
      have hs : (Finsupp.single e 1 + b).support = insert e b.support := by
        ext x
        rw [Finsupp.mem_support_iff, Finset.mem_insert, Finsupp.mem_support_iff]
        rw [Finsupp.mem_support_iff, not_not] at he
        simp only [Finsupp.add_apply, Finsupp.single_apply]
        constructor
        · intro h
          by_cases hx : e = x
          · left; exact hx.symm
          · right; simpa [hx] using h
        · rintro (h | h)
          · subst h; simp
          · split_ifs <;> omega
      unfold actT
      simp only [if_pos h1, if_pos hb]
      rw [hs, Finset.sum_powerset_insert he]
      congr 1
      refine Finset.sum_congr rfl fun W hW => ?_
      congr 1
      have hW' : e ∉ W := fun h => he (Finset.mem_powerset.mp hW h)
      have : insert e W = symmDiff {e} W := by
        rw [Finset.insert_eq, (Finset.disjoint_singleton_left.mpr hW').symmDiff_eq_sup]
        rfl
      rw [this, symmDiff_assoc]
  · have h1 : ¬ ∀ x, ((Finsupp.single e 1 + b : Sym2 ℕ →₀ ℕ)) x ≤ 1 := by
      intro h
      apply hb
      intro x
      have := h x
      simp only [Finsupp.add_apply] at this
      omega
    unfold actT
    rw [if_neg h1, if_neg hb, if_neg hb, add_zero]

/-- Composition of monomial operators is the operator of the product monomial (tex 2219, 10635–10655). PROVED. -/
theorem actT_comp (u v : Sym2 ℕ →₀ ℕ) (f : Finset (Sym2 ℕ) → ZMod 2) :
    actT u (actT v f) = actT (u + v) f := by
  induction u using Finsupp.induction with
  | zero => rw [actT_zero, zero_add]
  | single_add a k u' _ hk ih =>
    funext U
    by_cases hk1 : k = 1
    · subst hk1
      rw [actT_single_add, add_assoc, actT_single_add, ih]
    · have h2 : 2 ≤ k := by omega
      have hA : 2 ≤ ((Finsupp.single a k + u' : Sym2 ℕ →₀ ℕ)) a := by
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]; omega
      have hB : 2 ≤ ((Finsupp.single a k + u' + v : Sym2 ℕ →₀ ℕ)) a := by
        simp only [Finsupp.add_apply, Finsupp.single_eq_same]; omega
      rw [actT_eq_zero_of_two_le hA, actT_eq_zero_of_two_le hB]

/-- The action as a function: a monomial acts by its coefficient times the monomial
operator. -/
theorem act_monomial_fun (u : Sym2 ℕ →₀ ℕ) (a : ZMod 2) (f : Finset (Sym2 ℕ) → ZMod 2) :
    act (MvPolynomial.monomial u a) f = fun V => a * actT u f V := by
  funext V; exact act_monomial u a f V

/-- Multiplicativity: a product of polynomials acts by composition (tex 10651–10655).
PROVED. -/
theorem act_mul (p q : MvPolynomial (Sym2 ℕ) (ZMod 2)) (f : Finset (Sym2 ℕ) → ZMod 2) :
    act (p * q) f = act p (act q f) := by
  induction p using MvPolynomial.induction_on' with
  | monomial u a =>
    induction q using MvPolynomial.induction_on' with
    | monomial v b =>
      funext U
      rw [MvPolynomial.monomial_mul_monomial, act_monomial, act_monomial, act_monomial_fun,
        actT_smul_fun, actT_comp]
      ring
    | add q1 q2 h1 h2 =>
      funext U
      rw [mul_add, act_add, h1, h2, act_add, act_add_fun]
  | add p1 p2 h1 h2 =>
    rw [add_mul, act_add, h1, h2, act_add]

/-- The unit polynomial acts as the identity (tex 2219, 10635–10655). PROVED. -/
theorem act_one (f : Finset (Sym2 ℕ) → ZMod 2) : act 1 f = f := by
  funext U
  rw [← MvPolynomial.C_1, MvPolynomial.C_apply, act_monomial, actT_zero, one_mul]

/-- A constant acts by scalar multiplication (tex 2219, 10635–10655). PROVED. -/
theorem act_C (a : ZMod 2) (f : Finset (Sym2 ℕ) → ZMod 2) (U : Finset (Sym2 ℕ)) :
    act (MvPolynomial.C a) f U = a * f U := by
  rw [MvPolynomial.C_apply, act_monomial, actT_zero]

/-- One variable acts as the difference `Δ_e f (U) = f U + f (U ∆ {e})` (tex 2219). PROVED. -/
theorem act_X (e : Sym2 ℕ) (f : Finset (Sym2 ℕ) → ZMod 2) (U : Finset (Sym2 ℕ)) :
    act (MvPolynomial.X e) f U = f U + f (symmDiff U {e}) := by
  rw [MvPolynomial.X, act_monomial, one_mul, ← add_zero (Finsupp.single e 1), actT_single_add,
    actT_zero]

/-- Iterated difference over a finite set. -/
def dif (f : Finset (Sym2 ℕ) → ZMod 2) (S U : Finset (Sym2 ℕ)) : ZMod 2 :=
  ∑ W ∈ S.powerset, f (symmDiff U W)

/-- The indicator monomial of a finite set. -/
noncomputable def ind (S : Finset (Sym2 ℕ)) : Sym2 ℕ →₀ ℕ := ∑ e ∈ S, Finsupp.single e 1

lemma ind_apply (S : Finset (Sym2 ℕ)) (e : Sym2 ℕ) : ind S e = if e ∈ S then 1 else 0 := by
  classical
  unfold ind
  rw [Finsupp.finset_sum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

lemma ind_support (S : Finset (Sym2 ℕ)) : (ind S).support = S := by
  ext e
  rw [Finsupp.mem_support_iff, ind_apply]
  split_ifs with h <;> simp [h]

/-- A squarefree monomial acts by the iterated difference over its support (tex 2219, 10635–10655). PROVED. -/
theorem actT_ind (S : Finset (Sym2 ℕ)) (f : Finset (Sym2 ℕ) → ZMod 2) (U : Finset (Sym2 ℕ)) :
    actT (ind S) f U = dif f S U := by
  unfold actT dif
  rw [if_pos, ind_support]
  intro e
  rw [ind_apply]
  split_ifs <;> omega

/-- The action at `U` only reads `f` on the sets `U ∆ W` with `W` inside the variables of
`p` (tex 2219, 10635–10655). PROVED. -/
theorem act_congr_fun (p : MvPolynomial (Sym2 ℕ) (ZMod 2)) (f g : Finset (Sym2 ℕ) → ZMod 2)
    (U : Finset (Sym2 ℕ))
    (h : ∀ m ∈ p.support, ∀ W ⊆ m.support, f (symmDiff U W) = g (symmDiff U W)) :
    act p f U = act p g U := by
  unfold act
  refine Finset.sum_congr rfl fun m hm => ?_
  congr 1
  split_ifs
  · exact Finset.sum_congr rfl fun W hW => h m hm W (Finset.mem_powerset.mp hW)
  · rfl

end ZInQ.Manuscript.RC.Symbols
