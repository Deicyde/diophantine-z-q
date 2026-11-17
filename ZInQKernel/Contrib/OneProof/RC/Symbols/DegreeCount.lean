import ZInQKernel.Contrib.OneProof.RC.Symbols.Act

/-!
# Lane RC2: the degree count of App G (tex 10722–10784)

Generic tools: coefficient pairings with weights, the order filtration of polynomials,
leading parts of products, and tensor products of weights (a product of polynomials in
disjoint blocks of variables pairs with a product weight as the product of the pairings).
-/

namespace ZInQ.Manuscript.RC.Symbols

open Finset

section Generic

variable {τ : Type*}

/-- Coefficient pairing of a polynomial with a weight on monomials. -/
noncomputable def pairW (w : (τ →₀ ℕ) → ZMod 2) (q : MvPolynomial τ (ZMod 2)) : ZMod 2 :=
  ∑ m ∈ q.support, q.coeff m * w m

lemma pairW_eq_sum (w : (τ →₀ ℕ) → ZMod 2) (q : MvPolynomial τ (ZMod 2))
    {s : Finset (τ →₀ ℕ)} (hs : q.support ⊆ s) : pairW w q = ∑ m ∈ s, q.coeff m * w m := by
  unfold pairW
  apply Finset.sum_subset hs
  intro m _ hm
  rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]

lemma pairW_add (w : (τ →₀ ℕ) → ZMod 2) (p q : MvPolynomial τ (ZMod 2)) :
    pairW w (p + q) = pairW w p + pairW w q := by
  classical
  have h1 : (p + q).support ⊆ (p + q).support ∪ p.support ∪ q.support := by
    intro m hm; simp [hm]
  have h2 : p.support ⊆ (p + q).support ∪ p.support ∪ q.support := by
    intro m hm; simp [hm]
  have h3 : q.support ⊆ (p + q).support ∪ p.support ∪ q.support := by
    intro m hm; simp [hm]
  rw [pairW_eq_sum w _ h1, pairW_eq_sum w _ h2, pairW_eq_sum w _ h3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add, add_mul]

lemma pairW_zero (w : (τ →₀ ℕ) → ZMod 2) : pairW w 0 = 0 := by
  simp [pairW]

lemma pairW_sum {ι : Type*} (w : (τ →₀ ℕ) → ZMod 2) (s : Finset ι)
    (f : ι → MvPolynomial τ (ZMod 2)) : pairW w (∑ i ∈ s, f i) = ∑ i ∈ s, pairW w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairW_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairW_add, ih]

lemma pairW_monomial (w : (τ →₀ ℕ) → ZMod 2) (n : τ →₀ ℕ) (a : ZMod 2) :
    pairW w (MvPolynomial.monomial n a) = a * w n := by
  classical
  rw [pairW_eq_sum w _ (MvPolynomial.support_monomial_subset), Finset.sum_singleton,
    MvPolynomial.coeff_monomial, if_pos rfl]

/-- All monomials of degree `< k` have coefficient zero. -/
def HasOrd (Q : MvPolynomial τ (ZMod 2)) (k : ℕ) : Prop :=
  ∀ n : τ →₀ ℕ, n.degree < k → Q.coeff n = 0

lemma HasOrd.add {P Q : MvPolynomial τ (ZMod 2)} {k : ℕ} (hP : HasOrd P k) (hQ : HasOrd Q k) :
    HasOrd (P + Q) k := fun n hn => by
  rw [MvPolynomial.coeff_add, hP n hn, hQ n hn, add_zero]

lemma HasOrd.sub {P Q : MvPolynomial τ (ZMod 2)} {k : ℕ} (hP : HasOrd P k) (hQ : HasOrd Q k) :
    HasOrd (P - Q) k := fun n hn => by
  rw [MvPolynomial.coeff_sub, hP n hn, hQ n hn, sub_zero]

lemma HasOrd.mono {Q : MvPolynomial τ (ZMod 2)} {k k' : ℕ} (h : HasOrd Q k) (hk : k' ≤ k) :
    HasOrd Q k' := fun n hn => h n (by omega)

lemma hasOrd_zero_right (Q : MvPolynomial τ (ZMod 2)) : HasOrd Q 0 := fun _ hn =>
  absurd hn (Nat.not_lt_zero _)

lemma hasOrd_zero (k : ℕ) : HasOrd (0 : MvPolynomial τ (ZMod 2)) k := fun n _ => by
  simp

lemma hasOrd_add_self (Q : MvPolynomial τ (ZMod 2)) (k : ℕ) : HasOrd (Q + Q) k := fun n _ => by
  rw [MvPolynomial.coeff_add, zmod2_add_self]

lemma HasOrd.mul {P Q : MvPolynomial τ (ZMod 2)} {a b : ℕ} (hP : HasOrd P a) (hQ : HasOrd Q b) :
    HasOrd (P * Q) (a + b) := by
  classical
  intro n hn
  rw [MvPolynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  have hdeg : x.1.degree + x.2.degree = n.degree := by rw [← map_add, hx]
  by_cases h1 : x.1.degree < a
  · rw [hP _ h1, zero_mul]
  · rw [hQ _ (by omega), mul_zero]

lemma HasOrd.sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial τ (ZMod 2)) (k : ℕ)
    (h : ∀ i ∈ s, HasOrd (f i) k) : HasOrd (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact hasOrd_zero k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma degree_eq_one {n : τ →₀ ℕ} (h : n.degree = 1) : ∃ f, n = Finsupp.single f 1 := by
  have hn0 : n ≠ 0 := by
    intro h0; rw [h0, map_zero] at h; exact zero_ne_one h
  obtain ⟨f, hf⟩ := Finsupp.ne_iff.mp hn0
  have h1 : n f ≤ 1 := h ▸ Finsupp.le_degree f n
  have hf1 : n f = 1 := by simp only [Finsupp.coe_zero, Pi.zero_apply] at hf; omega
  refine ⟨f, ?_⟩
  have hle : Finsupp.single f 1 ≤ n := by
    rw [Finsupp.single_le_iff]; omega
  have hsplit : n = Finsupp.single f 1 + (n - Finsupp.single f 1) :=
    (add_tsub_cancel_of_le hle).symm
  have hdeg : (n - Finsupp.single f 1).degree = 0 := by
    have := congrArg Finsupp.degree hsplit
    rw [map_add, Finsupp.degree_single, h] at this
    omega
  rw [Finsupp.degree_eq_zero_iff] at hdeg
  rw [hsplit, hdeg, add_zero]

lemma hasOrd_one_iff (Q : MvPolynomial τ (ZMod 2)) :
    HasOrd Q 1 ↔ MvPolynomial.constantCoeff Q = 0 := by
  constructor
  · intro h
    rw [MvPolynomial.constantCoeff_eq]
    exact h 0 (by simp)
  · intro h n hn
    have : n = 0 := (Finsupp.degree_eq_zero_iff n).mp (by omega)
    rw [this, ← MvPolynomial.constantCoeff_eq, h]

lemma hasOrd_two_of (Q : MvPolynomial τ (ZMod 2)) (h0 : MvPolynomial.constantCoeff Q = 0)
    (h1 : ∀ f, Q.coeff (Finsupp.single f 1) = 0) : HasOrd Q 2 := by
  intro n hn
  rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | hn
  · exact (hasOrd_one_iff Q).mpr h0 n hn
  · obtain ⟨f, rfl⟩ := degree_eq_one hn
    exact h1 f

lemma degree_mapDomain {σ' : Type*} (f : τ → σ') (u : τ →₀ ℕ) :
    (u.mapDomain f).degree = u.degree := by
  induction u using Finsupp.induction with
  | zero => simp
  | single_add a b u' _ _ ih =>
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single, map_add, map_add, ih,
      Finsupp.degree_single, Finsupp.degree_single]

lemma HasOrd.rename {σ' : Type*} (f : τ → σ') {q : MvPolynomial τ (ZMod 2)} {k : ℕ}
    (h : HasOrd q k) : HasOrd (MvPolynomial.rename f q) k := by
  intro n hn
  by_contra hne
  obtain ⟨u, hu, hne'⟩ := MvPolynomial.coeff_rename_ne_zero f q n hne
  apply hne'
  apply h
  rw [← hu, degree_mapDomain] at hn
  exact hn

lemma hasOrd_X (v : τ) : HasOrd (MvPolynomial.X v : MvPolynomial τ (ZMod 2)) 1 := by
  rw [hasOrd_one_iff, MvPolynomial.constantCoeff_X]

/-- `f` is the leading part of `F` in degree `k`: `f` has order `k` and `F - f` order `k+1`. -/
def Lead (F f : MvPolynomial τ (ZMod 2)) (k : ℕ) : Prop :=
  HasOrd f k ∧ HasOrd (F - f) (k + 1)

lemma Lead.hasOrd {F f : MvPolynomial τ (ZMod 2)} {k : ℕ} (h : Lead F f k) : HasOrd F k := by
  have : F = f + (F - f) := by ring
  rw [this]
  exact h.1.add (h.2.mono (by omega))

lemma Lead.mul {F f G g : MvPolynomial τ (ZMod 2)} {a b : ℕ} (hF : Lead F f a)
    (hG : Lead G g b) : Lead (F * G) (f * g) (a + b) := by
  refine ⟨hF.1.mul hG.1, ?_⟩
  have : F * G - f * g = (F - f) * G + f * (G - g) := by ring
  rw [this]
  exact ((hF.2.mul hG.hasOrd).mono (by omega)).add ((hF.1.mul hG.2).mono (by omega))

lemma lead_one : Lead (1 : MvPolynomial τ (ZMod 2)) 1 0 :=
  ⟨hasOrd_zero_right _, by rw [sub_self]; exact hasOrd_zero _⟩

lemma Lead.prod {ι : Type*} (s : Finset ι) (F f : ι → MvPolynomial τ (ZMod 2)) (k : ι → ℕ)
    (h : ∀ i ∈ s, Lead (F i) (f i) (k i)) :
    Lead (∏ i ∈ s, F i) (∏ i ∈ s, f i) (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty]; exact lead_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

lemma Lead.rename {σ' : Type*} (g : τ → σ') {F f : MvPolynomial τ (ZMod 2)} {k : ℕ}
    (h : Lead F f k) : Lead (MvPolynomial.rename g F) (MvPolynomial.rename g f) k :=
  ⟨h.1.rename g, by rw [← map_sub]; exact h.2.rename g⟩

lemma lead_of_constantCoeff_one (F : MvPolynomial τ (ZMod 2))
    (h : MvPolynomial.constantCoeff F = 1) : Lead F 1 0 :=
  ⟨hasOrd_zero_right _, by rw [hasOrd_one_iff, map_sub, h, map_one, sub_self]⟩

/-- First-order approximation of a polynomial with constant coefficient one. -/
def Approx1 (F u : MvPolynomial τ (ZMod 2)) : Prop :=
  HasOrd u 1 ∧ HasOrd (F - (1 + u)) 2

lemma Approx1.prod {ι : Type*} (s : Finset ι) (F u : ι → MvPolynomial τ (ZMod 2))
    (h : ∀ i ∈ s, Approx1 (F i) (u i)) : Approx1 (∏ i ∈ s, F i) (∑ i ∈ s, u i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty]
    exact ⟨hasOrd_zero _, by rw [add_zero, sub_self]; exact hasOrd_zero _⟩
  | insert a s ha ih =>
    have ih' := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    have ha' := h a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    refine ⟨ha'.1.add ih'.1, ?_⟩
    have : F a * ∏ i ∈ s, F i - (1 + (u a + ∑ i ∈ s, u i)) =
        (F a - (1 + u a)) * (∏ i ∈ s, F i) + (1 + u a) * (∏ i ∈ s, F i - (1 + ∑ i ∈ s, u i))
          + u a * ∑ i ∈ s, u i := by ring
    rw [this]
    have hP : HasOrd (∏ i ∈ s, F i) 0 := hasOrd_zero_right _
    exact (((ha'.2.mul hP)).add ((hasOrd_zero_right _).mul ih'.2 |>.mono (by omega))).add
      (ha'.1.mul ih'.1)

lemma Approx1.rename {σ' : Type*} (g : τ → σ') {F u : MvPolynomial τ (ZMod 2)}
    (h : Approx1 F u) : Approx1 (MvPolynomial.rename g F) (MvPolynomial.rename g u) :=
  ⟨h.1.rename g, by
    have := h.2.rename g
    rwa [map_sub, map_add, map_one] at this⟩

lemma approx1_of_constantCoeff_one (F : MvPolynomial τ (ZMod 2))
    (h : MvPolynomial.constantCoeff F = 1) : Approx1 F (F - 1) :=
  ⟨by rw [hasOrd_one_iff, map_sub, h, map_one, sub_self],
    by rw [add_sub_cancel, sub_self]; exact hasOrd_zero _⟩

/-- Pairing with a weight that vanishes above degree `D` kills order `D + 1`. -/
lemma pairW_eq_zero_of_hasOrd (w : (τ →₀ ℕ) → ZMod 2) (D : ℕ)
    (hw : ∀ n : τ →₀ ℕ, D < n.degree → w n = 0) {Q : MvPolynomial τ (ZMod 2)}
    (hQ : HasOrd Q (D + 1)) : pairW w Q = 0 := by
  unfold pairW
  apply Finset.sum_eq_zero
  intro n _
  by_cases h : D < n.degree
  · rw [hw n h, mul_zero]
  · rw [hQ n (by omega), zero_mul]

lemma pairW_eq_of_lead (w : (τ →₀ ℕ) → ZMod 2) (D : ℕ)
    (hw : ∀ n : τ →₀ ℕ, D < n.degree → w n = 0) {Q q : MvPolynomial τ (ZMod 2)}
    (hQ : Lead Q q D) : pairW w Q = pairW w q := by
  have : Q = q + (Q - q) := by ring
  rw [this, pairW_add, pairW_eq_zero_of_hasOrd w D hw hQ.2, add_zero]

end Generic

section Tensor

variable {τ : Type*} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Product weight on the variables `ι × τ`. -/
noncomputable def tw (c : ι → (τ →₀ ℕ) → ZMod 2) (n : ι × τ →₀ ℕ) : ZMod 2 :=
  ∏ i, c i (n.curry i)

/-- The `i`-th block embedding. -/
noncomputable def emb (i : ι) : MvPolynomial τ (ZMod 2) →ₐ[ZMod 2] MvPolynomial (ι × τ) (ZMod 2) :=
  MvPolynomial.rename (Prod.mk i)

omit [Fintype ι] [DecidableEq ι] in
lemma curry_sum_mapDomain (s : Finset ι) (μ : ι → τ →₀ ℕ) (i : ι) (hi : i ∈ s) :
    (∑ j ∈ s, (μ j).mapDomain (Prod.mk j)).curry i = μ i := by
  ext e
  rw [Finsupp.curry_apply, Finsupp.finset_sum_apply, Finset.sum_eq_single i]
  · exact Finsupp.mapDomain_apply_of_injective (Prod.mk_right_injective i) _ _
  · intro j _ hji
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨x, hx⟩
    exact hji (congrArg Prod.fst hx)
  · intro h; exact absurd hi h

lemma prod_monomial' {κ : Type*} (s : Finset κ) (u : κ → τ →₀ ℕ) (a : κ → ZMod 2) :
    ∏ i ∈ s, (MvPolynomial.monomial (u i) (a i) : MvPolynomial τ (ZMod 2)) =
      MvPolynomial.monomial (∑ i ∈ s, u i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert b s hb ih =>
    rw [Finset.prod_insert hb, ih, MvPolynomial.monomial_mul_monomial, Finset.sum_insert hb,
      Finset.prod_insert hb]

/-- Factorization of the pairing on block products (tex 10736–10768). PROVED. -/
theorem pairW_tw_prod (c : ι → (τ →₀ ℕ) → ZMod 2) (q : ι → MvPolynomial τ (ZMod 2)) :
    pairW (tw c) (∏ i, emb i (q i)) = ∏ i, pairW (c i) (q i) := by
  have hq : ∀ i, emb i (q i) = ∑ m ∈ (q i).support,
      MvPolynomial.monomial (m.mapDomain (Prod.mk i)) ((q i).coeff m) := by
    intro i
    conv_lhs => rw [(q i).as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [emb, MvPolynomial.rename_monomial]
  simp_rw [hq]
  rw [Finset.prod_univ_sum, pairW_sum]
  have hr : ∀ i, pairW (c i) (q i) = ∑ m ∈ (q i).support, (q i).coeff m * c i m := fun i => rfl
  simp_rw [hr]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [prod_monomial', pairW_monomial, tw, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [curry_sum_mapDomain _ _ _ (Finset.mem_univ i)]

omit [DecidableEq ι] in
lemma degree_curry (n : ι × τ →₀ ℕ) : n.degree = ∑ i, (n.curry i).degree := by
  have h1 : n.degree = n.sum fun _ c => c := rfl
  have h2 := Finsupp.sum_curry_index n (fun _ _ c => c)
  rw [h1, ← h2, Finsupp.sum]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  rw [Finsupp.notMem_support_iff] at hi
  rw [hi]
  rfl

/-- A product weight vanishes above the sum of the degrees of its factors (tex 10736–10768). PROVED. -/
lemma tw_eq_zero (c : ι → (τ →₀ ℕ) → ZMod 2) (D : ι → ℕ)
    (hc : ∀ i (m : τ →₀ ℕ), D i < m.degree → c i m = 0) (n : ι × τ →₀ ℕ)
    (hn : ∑ i, D i < n.degree) : tw c n = 0 := by
  rw [degree_curry] at hn
  obtain ⟨i, _, hi⟩ := Finset.exists_lt_of_sum_lt hn
  exact Finset.prod_eq_zero (Finset.mem_univ i) (hc i _ hi)

end Tensor

section Factor

/-! ### One factor: the Möbius coefficients of a Boolean function and its degree -/

/-- The weight of a Boolean function: `m ↦ (X^m acting on g)(∅)`. -/
noncomputable def wt (g : Finset (Sym2 ℕ) → ZMod 2) (m : Sym2 ℕ →₀ ℕ) : ZMod 2 := actT m g ∅

lemma act_eq_pairW (q : MvPolynomial (Sym2 ℕ) (ZMod 2)) (g : Finset (Sym2 ℕ) → ZMod 2) :
    act q g ∅ = pairW (wt g) q :=
  act_eq_sum q g ∅ subset_rfl

lemma act_sum {κ : Type*} (s : Finset κ) (p : κ → MvPolynomial (Sym2 ℕ) (ZMod 2))
    (f : Finset (Sym2 ℕ) → ZMod 2) (U : Finset (Sym2 ℕ)) :
    act (∑ i ∈ s, p i) f U = ∑ i ∈ s, act (p i) f U := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, act_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, act_add]
    dsimp only
    rw [ih]

lemma act_one_add_X (e : Sym2 ℕ) (f : Finset (Sym2 ℕ) → ZMod 2) (U : Finset (Sym2 ℕ)) :
    act (1 + MvPolynomial.X e) f U = f (symmDiff U {e}) := by
  rw [act_add]
  dsimp only
  rw [act_one, act_X, ← add_assoc, zmod2_add_self, zero_add]

lemma act_prod_one_add_X (V : Finset (Sym2 ℕ)) (f : Finset (Sym2 ℕ) → ZMod 2)
    (U : Finset (Sym2 ℕ)) :
    act (∏ e ∈ V, (1 + MvPolynomial.X e)) f U = f (symmDiff U V) := by
  classical
  induction V using Finset.induction_on generalizing U with
  | empty =>
    rw [Finset.prod_empty, act_one]
    have h : symmDiff U (∅ : Finset (Sym2 ℕ)) = U := symmDiff_bot U
    rw [h]
  | insert a V ha ih =>
    rw [Finset.prod_insert ha, act_mul, act_one_add_X, ih]
    congr 1
    have : insert a V = symmDiff {a} V := by
      rw [Finset.insert_eq, (Finset.disjoint_singleton_left.mpr ha).symmDiff_eq_sup]
      rfl
    rw [this, symmDiff_assoc]

lemma ind_eq_sum (S : Finset (Sym2 ℕ)) : ind S = ∑ e ∈ S, Finsupp.single e 1 := rfl

lemma prod_X_eq (S : Finset (Sym2 ℕ)) :
    (∏ e ∈ S, MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2)) =
      MvPolynomial.monomial (ind S) 1 := by
  rw [ind_eq_sum, MvPolynomial.monomial_sum_one]
  rfl

lemma act_prod_X (S : Finset (Sym2 ℕ)) (f : Finset (Sym2 ℕ) → ZMod 2) (U : Finset (Sym2 ℕ)) :
    act (∏ e ∈ S, MvPolynomial.X e) f U = dif f S U := by
  rw [prod_X_eq, act_monomial, one_mul, actT_ind]

/-- Möbius inversion over `ZMod 2` (tex 10736–10768). PROVED. -/
theorem mobius (f : Finset (Sym2 ℕ) → ZMod 2) (V : Finset (Sym2 ℕ)) :
    f V = ∑ S ∈ V.powerset, dif f S ∅ := by
  have h1 : f V = act (∏ e ∈ V, (1 + MvPolynomial.X e)) f ∅ := by
    rw [act_prod_one_add_X]
    have : symmDiff (∅ : Finset (Sym2 ℕ)) V = V := bot_symmDiff V
    rw [this]
  rw [h1, Finset.prod_one_add, act_sum]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [act_prod_X]

lemma wt_ind (g : Finset (Sym2 ℕ) → ZMod 2) (S : Finset (Sym2 ℕ)) : wt g (ind S) = dif g S ∅ :=
  actT_ind S g ∅

lemma ind_injective : Function.Injective ind := by
  intro A B h
  rw [← ind_support A, ← ind_support B, h]

lemma degree_ind (S : Finset (Sym2 ℕ)) : (ind S).degree = S.card := by
  rw [ind_eq_sum, map_sum]
  simp

lemma symmDiff_inter_eq {E V : Finset (Sym2 ℕ)} {e : Sym2 ℕ} (he : e ∉ E) :
    symmDiff V {e} ∩ E = V ∩ E := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_symmDiff, Finset.mem_singleton]
  constructor
  · rintro ⟨h | h, hx⟩
    · exact ⟨h.1, hx⟩
    · exact absurd (h.1 ▸ hx) he
  · rintro ⟨h, hx⟩
    refine ⟨Or.inl ⟨h, fun hxe => he (hxe ▸ hx)⟩, hx⟩

lemma actT_shift (b : Sym2 ℕ →₀ ℕ) (g : Finset (Sym2 ℕ) → ZMod 2) (U : Finset (Sym2 ℕ))
    (e : Sym2 ℕ) (hg : ∀ V, g (symmDiff V {e}) = g V) :
    actT b g (symmDiff U {e}) = actT b g U := by
  unfold actT
  split_ifs
  · refine Finset.sum_congr rfl fun W _ => ?_
    rw [symmDiff_right_comm, hg]
  · rfl

lemma ind_insert {a : Sym2 ℕ} {S : Finset (Sym2 ℕ)} (ha : a ∉ S) :
    ind (insert a S) = Finsupp.single a 1 + ind S := by
  rw [ind_eq_sum, ind_eq_sum, Finset.sum_insert ha]

/-- A difference in a variable the function does not read vanishes (tex 10736–10768). PROVED. -/
lemma dif_eq_zero_of_not_subset (g : Finset (Sym2 ℕ) → ZMod 2) (E : Finset (Sym2 ℕ))
    (hE : ∀ U, g U = g (U ∩ E)) (S : Finset (Sym2 ℕ)) (hS : ¬ S ⊆ E) : dif g S ∅ = 0 := by
  obtain ⟨e, heS, heE⟩ := Finset.not_subset.mp hS
  have hg : ∀ V, g (symmDiff V {e}) = g V := fun V => by
    rw [hE, symmDiff_inter_eq heE, ← hE]
  rw [← wt_ind, wt, ← Finset.insert_erase heS, ind_insert (Finset.notMem_erase e S),
    actT_single_add, actT_shift _ _ _ _ hg, zmod2_add_self]

/-- The degree of the multilinear polynomial of `g` (variables in `E`). -/
noncomputable def dg (g : Finset (Sym2 ℕ) → ZMod 2) (E : Finset (Sym2 ℕ)) : ℕ :=
  ((E.powerset).filter (fun S => dif g S ∅ ≠ 0)).sup Finset.card

lemma card_le_dg {g : Finset (Sym2 ℕ) → ZMod 2} {E : Finset (Sym2 ℕ)}
    (hE : ∀ U, g U = g (U ∩ E)) {S : Finset (Sym2 ℕ)} (hS : dif g S ∅ ≠ 0) :
    S.card ≤ dg g E := by
  have hSE : S ⊆ E := by
    by_contra h; exact hS (dif_eq_zero_of_not_subset g E hE S h)
  exact Finset.le_sup (f := Finset.card) (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hSE, hS⟩)

/-- The weight vanishes above the degree (tex 10736–10768). PROVED. -/
lemma wt_eq_zero_of_lt {g : Finset (Sym2 ℕ) → ZMod 2} {E : Finset (Sym2 ℕ)}
    (hE : ∀ U, g U = g (U ∩ E)) (m : Sym2 ℕ →₀ ℕ) (hm : dg g E < m.degree) : wt g m = 0 := by
  unfold wt actT
  split_ifs with hsq
  · have hdeg : m.degree = m.support.card := by
      rw [Finsupp.degree_apply, Finset.card_eq_sum_ones]
      refine Finset.sum_congr rfl fun e he => ?_
      have := hsq e
      rw [Finsupp.mem_support_iff] at he
      omega
    by_contra hne
    have := card_le_dg hE (S := m.support) hne
    omega
  · rfl

/-- A nonzero function has a top coefficient (tex 10736–10768). PROVED. -/
lemma exists_top {g : Finset (Sym2 ℕ) → ZMod 2} {E : Finset (Sym2 ℕ)}
    (hE : ∀ U, g U = g (U ∩ E)) (hP : ∃ U, g U = 1) :
    ∃ S ⊆ E, S.card = dg g E ∧ dif g S ∅ ≠ 0 := by
  obtain ⟨U, hU⟩ := hP
  have hne : (∑ S ∈ (U ∩ E).powerset, dif g S ∅) ≠ 0 := by
    rw [← mobius, ← hE, hU]; exact one_ne_zero
  obtain ⟨S0, hS0, hS0'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hS0E : S0 ⊆ E := (Finset.mem_powerset.mp hS0).trans Finset.inter_subset_right
  have hnonempty : ((E.powerset).filter (fun S => dif g S ∅ ≠ 0)).Nonempty :=
    ⟨S0, Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hS0E, hS0'⟩⟩
  obtain ⟨S, hS, hSc⟩ := Finset.exists_mem_eq_sup _ hnonempty Finset.card
  rw [Finset.mem_filter, Finset.mem_powerset] at hS
  exact ⟨S, hS.1, hSc.symm, hS.2⟩

end Factor

section Pair

/-! ### One address: a coefficient-one monomial of the product of the two top parts -/

/-- Coefficients of the top homogeneous part. -/
noncomputable def topc (g : Finset (Sym2 ℕ) → ZMod 2) (d : ℕ) (A : Finset (Sym2 ℕ)) : ZMod 2 :=
  if A.card = d then dif g A ∅ else 0

lemma zmod2_eq_one_of_ne_zero {x : ZMod 2} (h : x ≠ 0) : x = 1 := by
  fin_cases x
  · exact absurd rfl h
  · rfl

lemma ind_add_ind (A B : Finset (Sym2 ℕ)) :
    ind A + ind B = ind (A ∩ B) + ind (A ∩ B) + ind (symmDiff A B) := by
  ext e
  simp only [Finsupp.add_apply, ind_apply, Finset.mem_inter, Finset.mem_symmDiff]
  by_cases hA : e ∈ A <;> by_cases hB : e ∈ B <;> simp [hA, hB]

lemma card_add_card (A B : Finset (Sym2 ℕ)) :
    A.card + B.card = 2 * (A ∩ B).card + (symmDiff A B).card := by
  have h1 := Finset.card_union_add_card_inter A B
  have h2 : (A ∪ B).card = (symmDiff A B).card + (A ∩ B).card := by
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_symmDiff, Finset.mem_inter]
      tauto
    · rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_symmDiff, Finset.mem_inter] at hx hx'
      tauto
  omega

lemma pair_set_ids (N2 N1 T : Finset (Sym2 ℕ)) (hd : Disjoint N2 N1) (hT : T ⊆ N1) :
    (N2 ∪ T) ∩ (N2 ∪ (N1 \ T)) = N2 ∧ symmDiff (N2 ∪ T) (N2 ∪ (N1 \ T)) = N1 ∧
      (N2 ∪ T) \ (N2 ∪ (N1 \ T)) = T := by
  rw [Finset.disjoint_left] at hd
  refine ⟨?_, ?_, ?_⟩ <;> ext a <;>
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_symmDiff] <;>
    have h1 := @hd a <;> have h2 := @hT a <;> tauto

lemma pair_set_ids' (A B : Finset (Sym2 ℕ)) :
    (A ∩ B) ∪ (A \ B) = A ∧ (A ∩ B) ∪ (symmDiff A B \ (A \ B)) = B := by
  refine ⟨?_, ?_⟩ <;> ext a <;>
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff, Finset.mem_symmDiff] <;>
    tauto

/-- **One address** (tex 10726–10735, 10760–10768): there are disjoint sets `N2` (exponent two)
and `N1` (exponent one) of total weight `d₁ + d₂` such that the coefficient of
`∏_{N2} X_e² ∏_{N1} X_e` in the product of the two top parts, written as the sum over the
distributions of the exponent-one variables, is one. Uses that the polynomial ring is a
domain. PROVED. -/
theorem exists_pair (g0 g1 : Finset (Sym2 ℕ) → ZMod 2) (E : Finset (Sym2 ℕ))
    (hE0 : ∀ U, g0 U = g0 (U ∩ E)) (hE1 : ∀ U, g1 U = g1 (U ∩ E))
    (hP0 : ∃ U, g0 U = 1) (hP1 : ∃ U, g1 U = 1) :
    ∃ N2 N1 : Finset (Sym2 ℕ), Disjoint N2 N1 ∧ N2 ⊆ E ∧ N1 ⊆ E ∧
      2 * N2.card + N1.card = dg g0 E + dg g1 E ∧
      ∑ T ∈ N1.powerset, dif g0 (N2 ∪ T) ∅ * dif g1 (N2 ∪ (N1 \ T)) ∅ = 1 := by
  classical
  set d0 := dg g0 E with hd0
  set d1 := dg g1 E with hd1
  let H : (Finset (Sym2 ℕ) → ZMod 2) → ℕ → MvPolynomial (Sym2 ℕ) (ZMod 2) := fun g d =>
    ∑ A ∈ E.powerset, MvPolynomial.monomial (ind A) (topc g d A)
  have hcoeff : ∀ g d S, S ∈ E.powerset → (H g d).coeff (ind S) = topc g d S := by
    intro g d S hS
    simp only [H, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single S]
    · simp
    · intro A _ hAS; rw [if_neg]; intro h; exact hAS (ind_injective h)
    · intro h; exact absurd hS h
  have hne : ∀ g, (∀ U, g U = g (U ∩ E)) → (∃ U, g U = 1) → H g (dg g E) ≠ 0 := by
    intro g hE hP h0
    obtain ⟨S, hSE, hSc, hS⟩ := exists_top hE hP
    have := hcoeff g (dg g E) S (Finset.mem_powerset.mpr hSE)
    rw [h0, topc, if_pos hSc] at this
    simp only [MvPolynomial.coeff_zero] at this
    exact hS this.symm
  have hprod : H g0 d0 * H g1 d1 ≠ 0 := mul_ne_zero (hne g0 hE0 hP0) (hne g1 hE1 hP1)
  let w : Finset (Sym2 ℕ) × Finset (Sym2 ℕ) → ZMod 2 := fun x =>
    topc g0 d0 x.1 * topc g1 d1 x.2
  let π : Finset (Sym2 ℕ) × Finset (Sym2 ℕ) → Finset (Sym2 ℕ) × Finset (Sym2 ℕ) := fun x =>
    (x.1 ∩ x.2, symmDiff x.1 x.2)
  let Mf : Finset (Sym2 ℕ) × Finset (Sym2 ℕ) → Sym2 ℕ →₀ ℕ := fun q =>
    ind q.1 + ind q.1 + ind q.2
  have hexp : H g0 d0 * H g1 d1 =
      ∑ x ∈ E.powerset ×ˢ E.powerset, MvPolynomial.monomial (Mf (π x)) (w x) := by
    simp only [H]
    rw [Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
    rw [MvPolynomial.monomial_mul_monomial]
    simp only [Mf, π, w]
    rw [ind_add_ind]
  have hfib : ∃ q ∈ (E.powerset ×ˢ E.powerset).image π,
      ∑ x ∈ (E.powerset ×ˢ E.powerset).filter (fun x => π x = q), w x ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hprod
    rw [hexp, ← Finset.sum_fiberwise_of_maps_to (g := π)
      (t := (E.powerset ×ˢ E.powerset).image π) (fun x hx => Finset.mem_image_of_mem π hx)]
    apply Finset.sum_eq_zero
    intro q hq
    have hc : ∀ x ∈ (E.powerset ×ˢ E.powerset).filter (fun x => π x = q),
        MvPolynomial.monomial (Mf (π x)) (w x) = MvPolynomial.monomial (Mf q) (w x) :=
      fun x hx => by rw [(Finset.mem_filter.mp hx).2]
    rw [Finset.sum_congr rfl hc, ← map_sum, hcon q hq, map_zero]
  obtain ⟨q, hq, hsum⟩ := hfib
  obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.mp hq
  rw [Finset.mem_product, Finset.mem_powerset, Finset.mem_powerset] at hx0
  set N2 := x0.1 ∩ x0.2 with hN2
  set N1 := symmDiff x0.1 x0.2 with hN1
  have hdisj : Disjoint N2 N1 := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    simp only [hN2, hN1, Finset.mem_inter, Finset.mem_symmDiff] at ha ha'
    tauto
  have hN2E : N2 ⊆ E := Finset.inter_subset_left.trans hx0.1
  have hN1E : N1 ⊆ E := by
    intro a ha
    simp only [hN1, Finset.mem_symmDiff] at ha
    rcases ha with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact hx0.1 ha
    · exact hx0.2 ha
  -- the degree condition, from a nonzero term of the fibre sum
  obtain ⟨x, hx, hwx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  rw [Finset.mem_filter] at hx
  have hx1 : x.1.card = d0 := by
    by_contra h; apply hwx; simp only [w, topc, if_neg h, zero_mul]
  have hx2 : x.2.card = d1 := by
    by_contra h; apply hwx; simp only [w, topc, if_neg h, mul_zero]
  have hdeg : 2 * N2.card + N1.card = d0 + d1 := by
    have := card_add_card x.1 x.2
    have hπ : x.1 ∩ x.2 = N2 ∧ symmDiff x.1 x.2 = N1 := Prod.ext_iff.mp hx.2
    rw [hπ.1, hπ.2, hx1, hx2] at this
    omega
  refine ⟨N2, N1, hdisj, hN2E, hN1E, hdeg, ?_⟩
  -- step a: replace the Möbius coefficients by the top coefficients
  have hstepa : ∑ T ∈ N1.powerset, dif g0 (N2 ∪ T) ∅ * dif g1 (N2 ∪ (N1 \ T)) ∅ =
      ∑ T ∈ N1.powerset, topc g0 d0 (N2 ∪ T) * topc g1 d1 (N2 ∪ (N1 \ T)) := by
    refine Finset.sum_congr rfl fun T hT => ?_
    rw [Finset.mem_powerset] at hT
    have hc1 : (N2 ∪ T).card = N2.card + T.card :=
      Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right hT hdisj)
    have hc2 : (N2 ∪ (N1 \ T)).card = N2.card + (N1.card - T.card) := by
      rw [Finset.card_union_of_disjoint (Finset.disjoint_of_subset_right Finset.sdiff_subset hdisj),
        Finset.card_sdiff_of_subset hT]
    have hTc : T.card ≤ N1.card := Finset.card_le_card hT
    unfold topc
    by_cases h0 : (N2 ∪ T).card = d0
    · rw [if_pos h0, if_pos (by omega)]
    · rw [if_neg h0, zero_mul]
      rcases Nat.lt_or_gt_of_ne h0 with h | h
      · have : dif g1 (N2 ∪ (N1 \ T)) ∅ = 0 := by
          by_contra hne'; have := card_le_dg hE1 hne'; omega
        rw [this, mul_zero]
      · have : dif g0 (N2 ∪ T) ∅ = 0 := by
          by_contra hne'; have := card_le_dg hE0 hne'; omega
        rw [this, zero_mul]
  -- step b: the distributions of exponent-one variables are the fibre
  have hstepb : ∑ T ∈ N1.powerset, topc g0 d0 (N2 ∪ T) * topc g1 d1 (N2 ∪ (N1 \ T)) =
      ∑ x ∈ (E.powerset ×ˢ E.powerset).filter (fun x => π x = π x0), w x := by
    refine Finset.sum_nbij' (fun T => (N2 ∪ T, N2 ∪ (N1 \ T))) (fun x => x.1 \ x.2)
      ?_ ?_ ?_ ?_ ?_
    · intro T hT
      rw [Finset.mem_powerset] at hT
      obtain ⟨i1, i2, _⟩ := pair_set_ids N2 N1 T hdisj hT
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_powerset,
        Finset.mem_powerset]
      refine ⟨⟨Finset.union_subset hN2E (hT.trans hN1E),
        Finset.union_subset hN2E (Finset.sdiff_subset.trans hN1E)⟩, ?_⟩
      simp only [π]
      rw [i1, i2]
    · intro x hx
      rw [Finset.mem_filter] at hx
      have hπ : x.1 ∩ x.2 = N2 ∧ symmDiff x.1 x.2 = N1 := Prod.ext_iff.mp hx.2
      rw [Finset.mem_powerset, ← hπ.2]
      intro a ha
      simp only [Finset.mem_sdiff] at ha
      simp only [Finset.mem_symmDiff]
      tauto
    · intro T hT
      rw [Finset.mem_powerset] at hT
      exact (pair_set_ids N2 N1 T hdisj hT).2.2
    · intro x hx
      rw [Finset.mem_filter] at hx
      have hπ : x.1 ∩ x.2 = N2 ∧ symmDiff x.1 x.2 = N1 := Prod.ext_iff.mp hx.2
      rw [← hπ.1, ← hπ.2, (pair_set_ids' x.1 x.2).1, (pair_set_ids' x.1 x.2).2]
    · intro T _
      rfl
  rw [hstepa, hstepb]
  exact zmod2_eq_one_of_ne_zero hsum

end Pair

section Programs

/-! ### Programs, as in the target statements -/

/-- A singular program at target `x` for the pair `e` (tex 10696–10701). -/
def IsSingularProgram {Y : Type*} (x : Y) (e : Sym2 ℕ)
    (O : Y → MvPolynomial (Sym2 ℕ) (ZMod 2)) : Prop :=
  MvPolynomial.constantCoeff (O x) = 0 ∧
    (∀ f, (O x).coeff (Finsupp.single f 1) = if f = e then 1 else 0) ∧
    ∀ y, y ≠ x → MvPolynomial.constantCoeff (O y) = 1

open Classical in
/-- A varying program pair at target `x` for the pair `e` (tex 10704–10720). -/
def IsVaryingProgram {Y : Type*} (x : Y) (e : Sym2 ℕ)
    (O : ZMod 2 → Y → MvPolynomial (Sym2 ℕ) (ZMod 2)) : Prop :=
  (∀ ε y, MvPolynomial.constantCoeff (O ε y) = 1) ∧
    ∀ y f, (O 0 y).coeff (Finsupp.single f 1) + (O 1 y).coeff (Finsupp.single f 1) =
      if y = x ∧ f = e then 1 else 0

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Lift of a family of address polynomials to the doubled variables: the block `(y, s)`
carries the polynomial at `y`, for both symbols `s`. -/
noncomputable def liftF (F : Y → MvPolynomial (Sym2 ℕ) (ZMod 2)) :
    MvPolynomial (Y × (Fin 2 × Sym2 ℕ)) (ZMod 2) :=
  ∏ y, emb y (∏ s : Fin 2, emb s (F y))

/-- The linear analogue of `liftF`. -/
noncomputable def linF (F : Y → MvPolynomial (Sym2 ℕ) (ZMod 2)) :
    MvPolynomial (Y × (Fin 2 × Sym2 ℕ)) (ZMod 2) :=
  ∑ y, emb y (∑ s : Fin 2, emb s (F y))

/-- The product weight of all factors. -/
noncomputable def W2 (P : Fin 2 → Y → Finset (Sym2 ℕ) → ZMod 2) :
    (Y × (Fin 2 × Sym2 ℕ) →₀ ℕ) → ZMod 2 :=
  tw (fun y => tw (fun s => wt (P s y)))

lemma liftF_mul (F G : Y → MvPolynomial (Sym2 ℕ) (ZMod 2)) :
    liftF (fun y => F y * G y) = liftF F * liftF G := by
  unfold liftF
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [← map_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_mul]

lemma liftF_one : liftF (fun _ : Y => (1 : MvPolynomial (Sym2 ℕ) (ZMod 2))) = 1 := by
  simp [liftF]

lemma liftF_prod {κ : Type*} (t : Finset κ) (F : κ → Y → MvPolynomial (Sym2 ℕ) (ZMod 2)) :
    liftF (fun y => ∏ j ∈ t, F j y) = ∏ j ∈ t, liftF (F j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact liftF_one
  | insert a t ha ih =>
    simp only [Finset.prod_insert ha]
    rw [liftF_mul (F a) (fun y => ∏ j ∈ t, F j y), ih]

lemma linF_add_sub (G0 G1 G2 : Y → MvPolynomial (Sym2 ℕ) (ZMod 2)) :
    linF (fun y => G0 y + G1 y - G2 y) = linF G0 + linF G1 - linF G2 := by
  unfold linF
  simp only [map_add, map_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The product of the actions on all factors is one pairing in the doubled variables. -/
lemma prod_act_eq (P : Fin 2 → Y → Finset (Sym2 ℕ) → ZMod 2)
    (F : Y → MvPolynomial (Sym2 ℕ) (ZMod 2)) :
    ∏ y, ∏ s : Fin 2, act (F y) (P s y) ∅ = pairW (W2 P) (liftF F) := by
  unfold W2 liftF
  rw [pairW_tw_prod]
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [pairW_tw_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [act_eq_pairW]

lemma lead_liftF (F f : Y → MvPolynomial (Sym2 ℕ) (ZMod 2)) (k : Y → ℕ)
    (h : ∀ y, Lead (F y) (f y) (k y)) :
    Lead (liftF F) (liftF f) (∑ y, ∑ _s : Fin 2, k y) := by
  unfold liftF
  apply Lead.prod
  intro y _
  exact Lead.rename (Prod.mk y)
    (Lead.prod _ _ _ _ fun s _ => (h y).rename (Prod.mk s))

lemma approx_liftF (F : Y → MvPolynomial (Sym2 ℕ) (ZMod 2))
    (h : ∀ y, MvPolynomial.constantCoeff (F y) = 1) :
    Approx1 (liftF F) (linF (fun y => F y - 1)) := by
  unfold liftF linF
  apply Approx1.prod
  intro y _
  exact Approx1.rename (Prod.mk y) (Approx1.prod _ _ _ fun s _ =>
    Approx1.rename (Prod.mk s) (approx1_of_constantCoeff_one (F y) (h y)))

lemma hasOrd_linF (G : Y → MvPolynomial (Sym2 ℕ) (ZMod 2)) (k : ℕ) (h : ∀ y, HasOrd (G y) k) :
    HasOrd (linF G) k := by
  unfold linF
  apply HasOrd.sum
  intro y _
  exact HasOrd.rename (Prod.mk y) (HasOrd.sum _ _ _ fun s _ => (h y).rename (Prod.mk s))

lemma single_ne_zero' (f : Sym2 ℕ) : (0 : Sym2 ℕ →₀ ℕ) ≠ Finsupp.single f 1 :=
  (Finsupp.single_ne_zero.mpr one_ne_zero).symm

/-- Leading part of a singular program at each address (tex 10736–10768). PROVED. -/
lemma lead_singular {x : Y} {e : Sym2 ℕ} {O : Y → MvPolynomial (Sym2 ℕ) (ZMod 2)}
    (hS : IsSingularProgram x e O) (y : Y) :
    Lead (O y) (if y = x then MvPolynomial.X e else 1) (if y = x then 1 else 0) := by
  split_ifs with hy
  · subst hy
    refine ⟨hasOrd_X e, hasOrd_two_of _ ?_ ?_⟩
    · rw [map_sub, hS.1, MvPolynomial.constantCoeff_X, sub_zero]
    · intro f
      rw [MvPolynomial.coeff_sub, hS.2.1 f, MvPolynomial.coeff_X']
      by_cases hf : f = e
      · subst hf; simp
      · rw [if_neg hf, if_neg, sub_zero]
        intro h; exact hf ((Finsupp.single_left_inj one_ne_zero).mp h).symm
  · exact lead_of_constantCoeff_one _ (hS.2.2 y hy)

/-- Leading part of the sum of a varying program pair: the linear term at its target, in
both symbol blocks (tex 10736–10768). PROVED. -/
lemma lead_varying {x : Y} {e : Sym2 ℕ} {O : ZMod 2 → Y → MvPolynomial (Sym2 ℕ) (ZMod 2)}
    (hV : IsVaryingProgram x e O) :
    Lead (liftF (O 0) + liftF (O 1)) (linF (fun y => if y = x then MvPolynomial.X e else 0)) 1 := by
  have hA0 := approx_liftF (O 0) (fun y => hV.1 0 y)
  have hA1 := approx_liftF (O 1) (fun y => hV.1 1 y)
  refine ⟨hasOrd_linF _ 1 (fun y => by
    split_ifs
    · exact hasOrd_X e
    · exact hasOrd_zero 1), ?_⟩
  have hG : HasOrd (linF (fun y => (O 0 y - 1) + (O 1 y - 1) -
      (if y = x then MvPolynomial.X e else 0))) 2 := by
    apply hasOrd_linF
    intro y
    apply hasOrd_two_of
    · rw [map_sub, map_add, map_sub, map_sub, hV.1 0 y, hV.1 1 y, map_one]
      split_ifs <;> simp
    · intro f
      have h2 := hV.2 y f
      simp only [MvPolynomial.coeff_sub, MvPolynomial.coeff_add, MvPolynomial.coeff_one,
        if_neg (single_ne_zero' f), sub_zero]
      by_cases hy : y = x
      · rw [if_pos hy, MvPolynomial.coeff_X']
        by_cases hf : f = e
        · subst hf
          rw [if_pos rfl]
          rw [if_pos ⟨hy, rfl⟩] at h2
          rw [h2, sub_self]
        · rw [if_neg (fun h => hf ((Finsupp.single_left_inj one_ne_zero).mp h).symm)]
          rw [if_neg (fun h => hf h.2)] at h2
          rw [h2, sub_zero]
      · rw [if_neg hy]
        rw [if_neg (fun h => hy h.1)] at h2
        simp [h2]
  have key : liftF (O 0) + liftF (O 1) - linF (fun y => if y = x then MvPolynomial.X e else 0) =
      (liftF (O 0) - (1 + linF (fun y => O 0 y - 1))) +
        (liftF (O 1) - (1 + linF (fun y => O 1 y - 1))) + (1 + 1) +
        linF (fun y => (O 0 y - 1) + (O 1 y - 1) - (if y = x then MvPolynomial.X e else 0)) := by
    rw [linF_add_sub]
    ring
  rw [key]
  exact ((hA0.2.add hA1.2).add (hasOrd_add_self 1 2)).add hG

lemma sum_ite_two (x : Y) : (∑ y, ∑ _s : Fin 2, (if y = x then 1 else 0 : ℕ)) = 2 := by
  simp [Finset.sum_ite_eq']

lemma liftF_leadS (p : Y × Sym2 ℕ) :
    liftF (fun y => if y = p.1 then (MvPolynomial.X p.2 : MvPolynomial (Sym2 ℕ) (ZMod 2))
      else 1) =
      emb p.1 (emb (0 : Fin 2) (MvPolynomial.X p.2) * emb (1 : Fin 2) (MvPolynomial.X p.2)) := by
  unfold liftF
  rw [Finset.prod_eq_single p.1]
  · dsimp only
    rw [if_pos rfl, Fin.prod_univ_two]
  · intro y _ hy
    simp [hy]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma linF_linS (p : Y × Sym2 ℕ) :
    linF (fun y => if y = p.1 then (MvPolynomial.X p.2 : MvPolynomial (Sym2 ℕ) (ZMod 2))
      else 0) =
      emb p.1 (emb (0 : Fin 2) (MvPolynomial.X p.2) + emb (1 : Fin 2) (MvPolynomial.X p.2)) := by
  unfold linF
  rw [Finset.sum_eq_single p.1]
  · dsimp only
    rw [if_pos rfl, Fin.sum_univ_two]
  · intro y _ hy
    simp [hy]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma pairwiseDisjoint_image (N : Y → Finset (Sym2 ℕ)) :
    ((Finset.univ : Finset Y) : Set Y).PairwiseDisjoint fun y => (N y).image (Prod.mk y) := by
  intro y1 _ y2 _ hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [Finset.mem_image] at hp hp'
  obtain ⟨a, _, rfl⟩ := hp
  obtain ⟨b, _, hb⟩ := hp'
  exact hne (congrArg Prod.fst hb).symm

lemma prod_biUnion_image {M : Type*} [CommMonoid M] (N : Y → Finset (Sym2 ℕ))
    (f : Y × Sym2 ℕ → M) :
    ∏ p ∈ Finset.univ.biUnion (fun y => (N y).image (Prod.mk y)), f p =
      ∏ y, ∏ e ∈ N y, f (y, e) := by
  rw [Finset.prod_biUnion (pairwiseDisjoint_image N)]
  refine Finset.prod_congr rfl fun y _ => ?_
  rw [Finset.prod_image]
  intro a _ b _ h
  exact Prod.mk_right_injective y h

lemma card_biUnion_image (N : Y → Finset (Sym2 ℕ)) :
    (Finset.univ.biUnion (fun y => (N y).image (Prod.mk y))).card = ∑ y, (N y).card := by
  rw [Finset.card_biUnion (pairwiseDisjoint_image N)]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact Finset.card_image_of_injective _ (Prod.mk_right_injective y)

lemma mem_biUnion_image (N : Y → Finset (Sym2 ℕ)) (p : Y × Sym2 ℕ) :
    p ∈ Finset.univ.biUnion (fun y => (N y).image (Prod.mk y)) ↔ p.2 ∈ N p.1 := by
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨y, _, hp⟩
    rw [Finset.mem_image] at hp
    obtain ⟨e, he, rfl⟩ := hp
    exact he
  · intro h
    exact ⟨p.1, Finset.mem_univ _, Finset.mem_image.mpr ⟨p.2, h, rfl⟩⟩

/-- Evaluation at one address of the minimum-cost operator (tex 10736–10768). PROVED. -/
lemma pairW_pair_eval (c : Fin 2 → (Sym2 ℕ →₀ ℕ) → ZMod 2) (N2 N1 : Finset (Sym2 ℕ))
    (hd : Disjoint N2 N1) :
    pairW (tw c) ((∏ e ∈ N2, (emb (0 : Fin 2) (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2)) *
        emb (1 : Fin 2) (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2)))) *
      ∏ e ∈ N1, (emb (0 : Fin 2) (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2)) +
        emb (1 : Fin 2) (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2)))) =
      ∑ T ∈ N1.powerset, c 0 (ind (N2 ∪ T)) * c 1 (ind (N2 ∪ (N1 \ T))) := by
  rw [Finset.prod_add, Finset.mul_sum, pairW_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.mem_powerset] at hT
  have hd1 : Disjoint N2 T := Finset.disjoint_of_subset_right hT hd
  have hd2 : Disjoint N2 (N1 \ T) := Finset.disjoint_of_subset_right Finset.sdiff_subset hd
  have key : (∏ e ∈ N2, (emb (0 : Fin 2) (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2)) *
        emb (1 : Fin 2) (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2)))) *
      ((∏ e ∈ T, emb (0 : Fin 2) (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2))) *
        ∏ e ∈ N1 \ T, emb (1 : Fin 2) (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2))) =
      ∏ s : Fin 2, emb s (∏ e ∈ (if s = 0 then N2 ∪ T else N2 ∪ (N1 \ T)),
        (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2))) := by
    rw [Fin.prod_univ_two, if_pos rfl, if_neg (by decide), map_prod, map_prod,
      Finset.prod_union hd1, Finset.prod_union hd2, Finset.prod_mul_distrib]
    ring
  rw [key, pairW_tw_prod, Fin.prod_univ_two, if_pos rfl, if_neg (by decide), prod_X_eq,
    prod_X_eq, pairW_monomial, pairW_monomial, one_mul, one_mul]

end Programs

section Main

lemma sum_zmod2 {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) : ∑ a, f a = f 0 + f 1 :=
  Fin.sum_univ_two f

/-- The degree count for given exponent sets at every address (tex 10736–10768): if the
selected coefficients are one, the sum over the choices of the product of all factors is one,
so one choice makes every factor one. PROVED. -/
theorem degree_count_core {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Fin 2 → Y → Finset (Sym2 ℕ) → ZMod 2) (E : Y → Finset (Sym2 ℕ))
    (hE : ∀ s y U, P s y U = P s y (U ∩ E y))
    (N2 N1 : Y → Finset (Sym2 ℕ)) (hdisj : ∀ y, Disjoint (N2 y) (N1 y))
    (hdeg : ∀ y, 2 * (N2 y).card + (N1 y).card = dg (P 0 y) (E y) + dg (P 1 y) (E y))
    (hval : ∀ y, ∑ T ∈ (N1 y).powerset,
      dif (P 0 y) (N2 y ∪ T) ∅ * dif (P 1 y) (N2 y ∪ (N1 y \ T)) ∅ = 1)
    (Os : Y × Sym2 ℕ → Y → MvPolynomial (Sym2 ℕ) (ZMod 2))
    (Ov : Y × Sym2 ℕ → ZMod 2 → Y → MvPolynomial (Sym2 ℕ) (ZMod 2))
    (hS : ∀ p ∈ Finset.univ.biUnion (fun y => (N2 y).image (Prod.mk y)),
      IsSingularProgram p.1 p.2 (Os p))
    (hV : ∀ p ∈ Finset.univ.biUnion (fun y => (N1 y).image (Prod.mk y)),
      IsVaryingProgram p.1 p.2 (Ov p)) :
    ∃ εv : Y × Sym2 ℕ → ZMod 2, ∀ s y,
      act ((∏ p ∈ Finset.univ.biUnion (fun y => (N2 y).image (Prod.mk y)), Os p y) *
        ∏ p ∈ Finset.univ.biUnion (fun y => (N1 y).image (Prod.mk y)), Ov p (εv p) y)
          (P s y) ∅ = 1 := by
  classical
  set Ns : Finset (Y × Sym2 ℕ) := Finset.univ.biUnion fun y => (N2 y).image (Prod.mk y)
    with hNs
  set Nv : Finset (Y × Sym2 ℕ) := Finset.univ.biUnion fun y => (N1 y).image (Prod.mk y)
    with hNv
  -- the choices, as functions on `Nv`
  let εx : ({p // p ∈ Nv} → ZMod 2) → Y × Sym2 ℕ → ZMod 2 := fun ε p =>
    if h : p ∈ Nv then ε ⟨p, h⟩ else 0
  set W := W2 P with hW
  set D : ℕ := ∑ y, ∑ s : Fin 2, dg (P s y) (E y) with hD
  have hWD : ∀ n, D < n.degree → W n = 0 := fun n hn =>
    tw_eq_zero _ (fun y => ∑ s : Fin 2, dg (P s y) (E y))
      (fun y m hm => tw_eq_zero _ (fun s => dg (P s y) (E y))
        (fun s m' hm' => wt_eq_zero_of_lt (hE s y) m' hm') m hm) n hn
  -- the operator after the sum over the choices, and its minimum-cost part
  set A := ∏ p ∈ Ns, liftF (Os p) with hA
  set C := ∏ p : {p // p ∈ Nv}, (liftF (Ov p.1 0) + liftF (Ov p.1 1)) with hC
  set Astar := ∏ p ∈ Ns, liftF (fun y => if y = p.1 then
    (MvPolynomial.X p.2 : MvPolynomial (Sym2 ℕ) (ZMod 2)) else 1) with hAstar
  set Cstar := ∏ p : {p // p ∈ Nv}, linF (fun y => if y = p.1.1 then
    (MvPolynomial.X p.1.2 : MvPolynomial (Sym2 ℕ) (ZMod 2)) else 0) with hCstar
  have hsum1 : ∑ ε : ({p // p ∈ Nv} → ZMod 2), ∏ y, ∏ s : Fin 2,
      act ((∏ p ∈ Ns, Os p y) * ∏ p ∈ Nv, Ov p (εx ε p) y) (P s y) ∅ = pairW W (A * C) := by
    have hl : ∀ ε : ({p // p ∈ Nv} → ZMod 2),
        liftF (fun y => (∏ p ∈ Ns, Os p y) * ∏ p ∈ Nv, Ov p (εx ε p) y) =
          A * ∏ p : {p // p ∈ Nv}, liftF (Ov p.1 (ε p)) := by
      intro ε
      rw [liftF_mul (fun y => ∏ p ∈ Ns, Os p y) (fun y => ∏ p ∈ Nv, Ov p (εx ε p) y),
        liftF_prod, liftF_prod (F := fun p y => Ov p (εx ε p) y)]
      congr 1
      rw [← Finset.prod_coe_sort Nv]
      refine Finset.prod_congr rfl fun p _ => ?_
      simp only [εx, dif_pos p.2]
    have h1 : ∀ ε : ({p // p ∈ Nv} → ZMod 2), ∏ y, ∏ s : Fin 2,
        act ((∏ p ∈ Ns, Os p y) * ∏ p ∈ Nv, Ov p (εx ε p) y) (P s y) ∅ =
          pairW W (A * ∏ p : {p // p ∈ Nv}, liftF (Ov p.1 (ε p))) := by
      intro ε
      rw [prod_act_eq P (fun y => (∏ p ∈ Ns, Os p y) * ∏ p ∈ Nv, Ov p (εx ε p) y), hl]
    have hCsum : C = ∑ ε : ({p // p ∈ Nv} → ZMod 2),
        ∏ p : {p // p ∈ Nv}, liftF (Ov p.1 (ε p)) := by
      rw [hC]
      have : ∀ p : {p // p ∈ Nv}, liftF (Ov p.1 0) + liftF (Ov p.1 1) =
          ∑ a : ZMod 2, liftF (Ov p.1 a) := fun p =>
        (sum_zmod2 (fun a : ZMod 2 => liftF (Ov p.1 a))).symm
      simp_rw [this]
      exact Fintype.prod_sum (fun (p : {p // p ∈ Nv}) (a : ZMod 2) => liftF (Ov p.1 a))
    rw [Finset.sum_congr rfl (fun ε _ => h1 ε), ← pairW_sum, ← Finset.mul_sum, hCsum]
  -- the leading part
  have hlead : Lead (A * C) (Astar * Cstar) (∑ p ∈ Ns, 2 + ∑ _p : {p // p ∈ Nv}, 1) := by
    apply Lead.mul
    · apply Lead.prod
      intro p hp
      have := lead_liftF (Os p) _ _ (lead_singular (hS p hp))
      rwa [sum_ite_two] at this
    · apply Lead.prod
      intro p _
      exact lead_varying (hV p.1 p.2)
  have hDeq : (∑ p ∈ Ns, 2 + ∑ _p : {p // p ∈ Nv}, 1) = D := by
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul,
      smul_eq_mul, mul_one, hNs, hNv, card_biUnion_image, card_biUnion_image, hD]
    simp only [Fin.sum_univ_two]
    rw [Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← hdeg y]
    ring
  rw [hDeq] at hlead
  have hstar : pairW W (Astar * Cstar) = 1 := by
    have hA' : Astar = ∏ y, emb y (∏ e ∈ N2 y, (emb (0 : Fin 2)
        (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2)) *
          emb (1 : Fin 2) (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2)))) := by
      rw [hAstar]
      simp_rw [liftF_leadS]
      rw [hNs, prod_biUnion_image]
      refine Finset.prod_congr rfl fun y _ => ?_
      rw [map_prod]
    have hC' : Cstar = ∏ y, emb y (∏ e ∈ N1 y, (emb (0 : Fin 2)
        (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2)) +
          emb (1 : Fin 2) (MvPolynomial.X e : MvPolynomial (Sym2 ℕ) (ZMod 2)))) := by
      rw [hCstar]
      simp_rw [linF_linS]
      rw [Finset.prod_coe_sort Nv (fun p => emb p.1 (emb (0 : Fin 2)
        (MvPolynomial.X p.2 : MvPolynomial (Sym2 ℕ) (ZMod 2)) +
          emb (1 : Fin 2) (MvPolynomial.X p.2 : MvPolynomial (Sym2 ℕ) (ZMod 2))))]
      rw [hNv, prod_biUnion_image]
      refine Finset.prod_congr rfl fun y _ => ?_
      rw [map_prod]
    rw [hA', hC', ← Finset.prod_mul_distrib]
    simp_rw [← map_mul]
    rw [hW, W2, pairW_tw_prod]
    apply Finset.prod_eq_one
    intro y _
    rw [pairW_pair_eval _ _ _ (hdisj y)]
    simp only [wt_ind]
    exact hval y
  have hsum : ∑ ε : ({p // p ∈ Nv} → ZMod 2), ∏ y, ∏ s : Fin 2,
      act ((∏ p ∈ Ns, Os p y) * ∏ p ∈ Nv, Ov p (εx ε p) y) (P s y) ∅ = 1 := by
    rw [hsum1, pairW_eq_of_lead W D hWD hlead, hstar]
  obtain ⟨ε, _, hε⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hsum]; exact one_ne_zero)
  refine ⟨εx ε, fun s y => ?_⟩
  have hy := Finset.prod_ne_zero_iff.mp hε y (Finset.mem_univ y)
  exact zmod2_eq_one_of_ne_zero (Finset.prod_ne_zero_iff.mp hy s (Finset.mem_univ s))

/-- **(G.1a): one choice for both symbols at every nonzero address** (tex 10722–10768).
For every address `y` choose, in the ordinary polynomial ring, a coefficient-one monomial of
the product of the two top homogeneous parts; install a singular program for each exponent-two
variable (`Ns`) and a varying program for each exponent-one variable (`Nv`). Then the sum over
the choices `ε` of the product of all factors equals the product of the selected coefficients,
which is one (the degree count: an operator part above the degree kills a factor, the minimum
costs add up to the available degree, and only minimum-cost terms survive); hence one choice
makes every factor one. PROVED. -/
theorem degree_count {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Fin 2 → Y → Finset (Sym2 ℕ) → ZMod 2) (E : Y → Finset (Sym2 ℕ))
    (hE : ∀ s y U, P s y U = P s y (U ∩ E y)) (hP : ∀ s y, ∃ U, P s y U = 1) :
    ∃ (Ns Nv : Finset (Y × Sym2 ℕ)), Disjoint Ns Nv ∧ (∀ p ∈ Ns ∪ Nv, p.2 ∈ E p.1) ∧
      ∀ (Os : Y × Sym2 ℕ → Y → MvPolynomial (Sym2 ℕ) (ZMod 2))
        (Ov : Y × Sym2 ℕ → ZMod 2 → Y → MvPolynomial (Sym2 ℕ) (ZMod 2)),
        (∀ p ∈ Ns, IsSingularProgram p.1 p.2 (Os p)) →
        (∀ p ∈ Nv, IsVaryingProgram p.1 p.2 (Ov p)) →
        ∃ εv : Y × Sym2 ℕ → ZMod 2, ∀ s y,
          act ((∏ p ∈ Ns, Os p y) * ∏ p ∈ Nv, Ov p (εv p) y) (P s y) ∅ = 1 := by
  classical
  have hpair := fun y => exists_pair (P 0 y) (P 1 y) (E y) (hE 0 y) (hE 1 y) (hP 0 y) (hP 1 y)
  choose N2 N1 hdisj hN2E hN1E hdeg hval using hpair
  refine ⟨Finset.univ.biUnion fun y => (N2 y).image (Prod.mk y),
    Finset.univ.biUnion fun y => (N1 y).image (Prod.mk y), ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro p hp hp'
    rw [mem_biUnion_image] at hp hp'
    exact Finset.disjoint_left.mp (hdisj p.1) hp hp'
  · intro p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rw [mem_biUnion_image] at hp; exact hN2E p.1 hp
    · rw [mem_biUnion_image] at hp; exact hN1E p.1 hp
  intro Os Ov hS hV
  exact degree_count_core P E hE N2 N1 hdisj hdeg hval Os Ov hS hV

/-- **The one-symbol specialization** (tex 10778–10784): choose a coefficient-one top
monomial of each nonzero `P_y` and put one singular program at `y` for each of its variables;
any extra degree kills the term, so exactly the selected top coefficient survives, and it is
one. Derived from `degree_count_core` with both symbols equal to `P` and no exponent-one
variables. PROVED. -/
theorem degree_count_one {Y : Type*} [Fintype Y] [DecidableEq Y]
    (P : Y → Finset (Sym2 ℕ) → ZMod 2) (E : Y → Finset (Sym2 ℕ))
    (hE : ∀ y U, P y U = P y (U ∩ E y)) (hP : ∀ y, ∃ U, P y U = 1) :
    ∃ Ns : Finset (Y × Sym2 ℕ), (∀ p ∈ Ns, p.2 ∈ E p.1) ∧
      ∀ Os : Y × Sym2 ℕ → Y → MvPolynomial (Sym2 ℕ) (ZMod 2),
        (∀ p ∈ Ns, IsSingularProgram p.1 p.2 (Os p)) →
        ∀ y, act (∏ p ∈ Ns, Os p y) (P y) ∅ = 1 := by
  classical
  have htop := fun y => exists_top (hE y) (hP y)
  choose S hSE hSc hSv using htop
  refine ⟨Finset.univ.biUnion (fun y => (S y).image (Prod.mk y)), ?_, ?_⟩
  · intro p hp
    rw [mem_biUnion_image] at hp
    exact hSE p.1 hp
  · intro Os hS y
    have hNv : Finset.univ.biUnion (fun y : Y => (∅ : Finset (Sym2 ℕ)).image (Prod.mk y)) = ∅ := by
      ext p; simp
    obtain ⟨εv, hεv⟩ := degree_count_core (fun _ y => P y) E (fun _ y U => hE y U) S
      (fun _ => ∅) (fun y => Finset.disjoint_empty_right _)
      (fun y => by rw [Finset.card_empty, hSc y]; ring)
      (fun y => by
        rw [Finset.powerset_empty, Finset.sum_singleton, Finset.union_empty, Finset.empty_sdiff,
          Finset.union_empty, zmod2_eq_one_of_ne_zero (hSv y), one_mul])
      Os (fun _ _ _ => 1) hS (fun p hp => by rw [hNv] at hp; exact absurd hp (Finset.notMem_empty p))
    have := hεv 0 y
    rw [hNv, Finset.prod_empty, mul_one] at this
    exact this

end Main

end ZInQ.Manuscript.RC.Symbols
