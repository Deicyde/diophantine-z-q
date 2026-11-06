import Mathlib

/-!
# Existential polynomials and calls

Polynomials live in `ℤ[X_i : i ∈ ℕ]` and every variable ranges over `ℚ`.

* `ZInQ.Syntax.ev x f` is the value of `f` at a rational assignment `x : ℕ → ℚ`.
* An `ExPoly` is a polynomial together with a parameter count `p` and a witness count `m`:
  its local variables `0, …, p-1` are parameters and `p, …, p+m-1` are witnesses.
  Its relation `ExPoly.Rel` holds at `a ∈ ℚ^p` when some `y ∈ ℚ^m` makes it vanish
  (variables of index at least `p + m` are set to `0`).
* `callPoly P p w g` is the call `P[g_0, …, g_{p-1}; w]`: the image of `P` under the
  substitution `X_i ↦ g_i` (`i < p`), `X_i ↦ X_{w+i-p}` (`i ≥ p`).

We also record variable-range bounds (`VarsLT`), a degree bound for substitution
(`totalDegree_bind₁_le`) and the final renaming into `MvPolynomial (Fin N) ℤ`.
-/

namespace ZInQ.Syntax

open MvPolynomial

/-- Integer polynomials in the variables `X i`, `i : ℕ`. -/
abbrev Poly : Type := MvPolynomial ℕ ℤ

/-! ### Evaluation -/

/-- Evaluation of an integer polynomial at a rational assignment. -/
noncomputable def ev (x : ℕ → ℚ) : Poly →+* ℚ := eval₂Hom (Int.castRingHom ℚ) x

theorem ev_apply (x : ℕ → ℚ) (f : Poly) : ev x f = eval₂ (Int.castRingHom ℚ) x f := rfl

@[simp] theorem ev_X (x : ℕ → ℚ) (i : ℕ) : ev x (X i) = x i := eval₂_X _ _ _

@[simp] theorem ev_C (x : ℕ → ℚ) (c : ℤ) : ev x (C c) = c := eval₂_C _ _ _

@[simp] theorem ev_ofNat (x : ℕ → ℚ) (n : ℕ) [n.AtLeastTwo] :
    ev x (no_index (OfNat.ofNat n : Poly)) = OfNat.ofNat n := map_ofNat _ n

/-- The value of a polynomial depends only on the values of its variables. -/
theorem ev_congr {x y : ℕ → ℚ} {f : Poly} (h : ∀ i ∈ f.vars, x i = y i) : ev x f = ev y f := by
  simp only [ev_apply]
  exact eval₂_congr _ _ _ fun {i} {c} hi hc =>
    h i ((mem_vars_iff_mem_support i).2 ⟨c, mem_support_iff.2 hc, hi⟩)

/-! ### Variable ranges -/

/-- Every variable of `f` satisfies `P`. -/
def VarsIn (f : Poly) (P : ℕ → Prop) : Prop := ∀ i ∈ f.vars, P i

namespace VarsIn

variable {P Q : ℕ → Prop}

theorem mono {f : Poly} (h : VarsIn f P) (hPQ : ∀ i, P i → Q i) : VarsIn f Q :=
  fun i hi => hPQ i (h i hi)

theorem of_subset {f g : Poly} (h : VarsIn g P) (hfg : f.vars ⊆ g.vars) : VarsIn f P :=
  fun i hi => h i (hfg hi)

theorem X {i : ℕ} (h : P i) : VarsIn (MvPolynomial.X i) P := by
  intro j hj
  rw [vars_X, Finset.mem_singleton] at hj
  exact hj ▸ h

theorem C (c : ℤ) (P : ℕ → Prop) : VarsIn (MvPolynomial.C c) P := by
  intro j hj
  rw [vars_C] at hj
  simp at hj

theorem intCast (c : ℤ) (P : ℕ → Prop) : VarsIn (c : Poly) P := by
  rw [← eq_intCast (MvPolynomial.C : ℤ →+* Poly) c]
  exact C c P

theorem zero (P : ℕ → Prop) : VarsIn 0 P := by simpa using C 0 P

theorem one (P : ℕ → Prop) : VarsIn 1 P := by simpa using C 1 P

theorem ofNat (k : ℕ) [k.AtLeastTwo] (P : ℕ → Prop) : VarsIn (OfNat.ofNat k : Poly) P := by
  rw [← map_ofNat (MvPolynomial.C : ℤ →+* Poly) k]
  exact C _ P

theorem add {f g : Poly} (hf : VarsIn f P) (hg : VarsIn g P) : VarsIn (f + g) P := by
  classical
  intro i hi
  rcases Finset.mem_union.1 (vars_add_subset f g hi) with h | h
  exacts [hf i h, hg i h]

theorem mul {f g : Poly} (hf : VarsIn f P) (hg : VarsIn g P) : VarsIn (f * g) P := by
  classical
  intro i hi
  rcases Finset.mem_union.1 (vars_mul f g hi) with h | h
  exacts [hf i h, hg i h]

theorem neg {f : Poly} (hf : VarsIn f P) : VarsIn (-f) P := by
  intro i hi
  rw [vars_neg] at hi
  exact hf i hi

theorem sub {f g : Poly} (hf : VarsIn f P) (hg : VarsIn g P) : VarsIn (f - g) P := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem pow {f : Poly} (hf : VarsIn f P) (k : ℕ) : VarsIn (f ^ k) P :=
  fun i hi => hf i (vars_pow f k hi)

theorem list_sum {l : List Poly} (h : ∀ f ∈ l, VarsIn f P) : VarsIn l.sum P := by
  induction l with
  | nil => exact zero P
  | cons f l ih =>
    rw [List.sum_cons]
    exact (h f List.mem_cons_self).add (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

theorem list_prod {l : List Poly} (h : ∀ f ∈ l, VarsIn f P) : VarsIn l.prod P := by
  induction l with
  | nil => exact one P
  | cons f l ih =>
    rw [List.prod_cons]
    exact (h f List.mem_cons_self).mul (ih fun g hg => h g (List.mem_cons_of_mem _ hg))

end VarsIn

/-- Every variable of `f` has index below `n`. -/
def VarsLT (f : Poly) (n : ℕ) : Prop := VarsIn f (· < n)

namespace VarsLT

theorem mono {f : Poly} {n n' : ℕ} (h : VarsLT f n) (hn : n ≤ n') : VarsLT f n' :=
  VarsIn.mono h fun _ hi => lt_of_lt_of_le hi hn

theorem of_subset {f g : Poly} {n : ℕ} (h : VarsLT g n) (hfg : f.vars ⊆ g.vars) : VarsLT f n :=
  VarsIn.of_subset h hfg

theorem X {i n : ℕ} (h : i < n) : VarsLT (MvPolynomial.X i) n := VarsIn.X h

theorem C (c : ℤ) (n : ℕ) : VarsLT (MvPolynomial.C c) n := VarsIn.C c _

theorem intCast (c : ℤ) (n : ℕ) : VarsLT (c : Poly) n := VarsIn.intCast c _

theorem zero (n : ℕ) : VarsLT 0 n := VarsIn.zero _

theorem one (n : ℕ) : VarsLT 1 n := VarsIn.one _

theorem ofNat (k n : ℕ) [k.AtLeastTwo] : VarsLT (OfNat.ofNat k : Poly) n := VarsIn.ofNat k _

theorem add {f g : Poly} {n : ℕ} (hf : VarsLT f n) (hg : VarsLT g n) : VarsLT (f + g) n :=
  VarsIn.add hf hg

theorem mul {f g : Poly} {n : ℕ} (hf : VarsLT f n) (hg : VarsLT g n) : VarsLT (f * g) n :=
  VarsIn.mul hf hg

theorem neg {f : Poly} {n : ℕ} (hf : VarsLT f n) : VarsLT (-f) n := VarsIn.neg hf

theorem sub {f g : Poly} {n : ℕ} (hf : VarsLT f n) (hg : VarsLT g n) : VarsLT (f - g) n :=
  VarsIn.sub hf hg

theorem pow {f : Poly} {n : ℕ} (hf : VarsLT f n) (k : ℕ) : VarsLT (f ^ k) n := VarsIn.pow hf k

theorem list_sum {l : List Poly} {n : ℕ} (h : ∀ f ∈ l, VarsLT f n) : VarsLT l.sum n :=
  VarsIn.list_sum h

theorem list_prod {l : List Poly} {n : ℕ} (h : ∀ f ∈ l, VarsLT f n) : VarsLT l.prod n :=
  VarsIn.list_prod h

end VarsLT

/-! ### Existential polynomials -/

/-- A polynomial with `params` parameters followed by `witnesses` witnesses. Templates and
recipes denote existential polynomials. -/
structure ExPoly where
  /-- The parameter count `p`; the parameters are `X_0, …, X_{p-1}`. -/
  params : ℕ
  /-- The witness count `m`; the witnesses are `X_p, …, X_{p+m-1}`. -/
  witnesses : ℕ
  /-- The polynomial. -/
  poly : Poly

/-- The assignment `(a_0, …, a_{p-1}, y_0, …, y_{m-1}, 0, 0, …)`. -/
def assign (p m : ℕ) (a : Fin p → ℚ) (y : Fin m → ℚ) (i : ℕ) : ℚ :=
  if h : i < p then a ⟨i, h⟩ else if h' : i - p < m then y ⟨i - p, h'⟩ else 0

theorem assign_of_lt {p m : ℕ} (a : Fin p → ℚ) (y : Fin m → ℚ) {i : ℕ} (h : i < p) :
    assign p m a y i = a ⟨i, h⟩ := by
  simp [assign, h]

theorem assign_add (p m : ℕ) (a : Fin p → ℚ) (y : Fin m → ℚ) (j : Fin m) :
    assign p m a y (p + j) = y j := by
  simp [assign]

namespace ExPoly

/-- The variable count `v = p + m`. -/
def varCount (τ : ExPoly) : ℕ := τ.params + τ.witnesses

/-- All variables of the polynomial have index below the variable count. -/
def WF (τ : ExPoly) : Prop := VarsLT τ.poly τ.varCount

/-- `Rel_τ(a)`: some rational witnesses make the polynomial vanish at the parameters `a`. -/
def Rel (τ : ExPoly) (a : Fin τ.params → ℚ) : Prop :=
  ∃ y : Fin τ.witnesses → ℚ, ev (assign τ.params τ.witnesses a y) τ.poly = 0

end ExPoly

/-! ### Calls -/

/-- The substitution of a call: `X_i ↦ g_i` for `i < p` and `X_i ↦ X_{w+i-p}` for `i ≥ p`. -/
noncomputable def callSubst (p w : ℕ) (g : Fin p → Poly) (i : ℕ) : Poly :=
  if h : i < p then g ⟨i, h⟩ else X (w + (i - p))

/-- The call `P[g_0, …, g_{p-1}; w]`: witness `p + j` of the callee becomes the caller's
variable `X_{w+j}`. -/
noncomputable def callPoly (P : Poly) (p w : ℕ) (g : Fin p → Poly) : Poly :=
  bind₁ (callSubst p w g) P

/-- The call `τ[g; w]` of an existential polynomial. -/
noncomputable def ExPoly.call (τ : ExPoly) (g : Fin τ.params → Poly) (w : ℕ) : Poly :=
  callPoly τ.poly τ.params w g

/-- Evaluation commutes with the substitution of a call. -/
theorem ev_callPoly (P : Poly) (p w : ℕ) (g : Fin p → Poly) (x : ℕ → ℚ) :
    ev x (callPoly P p w g) =
      ev (fun i => if h : i < p then ev x (g ⟨i, h⟩) else x (w + (i - p))) P := by
  simp only [ev, callPoly, eval₂Hom_bind₁]
  refine congrArg (fun f => eval₂Hom (Int.castRingHom ℚ) f P) (funext fun i => ?_)
  unfold callSubst
  split_ifs <;> simp

/-- **Evaluation of a call.** If all variables of `τ` lie below its variable count, then
`τ[g; w](x) = [[τ]](g_0(x), …, g_{p-1}(x), x_w, …, x_{w+m-1})`. -/
theorem ExPoly.ev_call {τ : ExPoly} (hτ : τ.WF) (g : Fin τ.params → Poly) (w : ℕ)
    (x : ℕ → ℚ) :
    ev x (τ.call g w) =
      ev (assign τ.params τ.witnesses (fun i => ev x (g i)) (fun j => x (w + j))) τ.poly := by
  rw [ExPoly.call, ev_callPoly]
  refine ev_congr fun i hi => ?_
  have hi' : i < τ.params + τ.witnesses := hτ i hi
  unfold assign
  split_ifs with h1 h2
  · rfl
  · rfl
  · omega

/-- The assignment `x[X_{w+j} ↦ y_j]`. -/
def blockUpdate (x : ℕ → ℚ) (w m : ℕ) (y : Fin m → ℚ) (i : ℕ) : ℚ :=
  if h : w ≤ i ∧ i - w < m then y ⟨i - w, h.2⟩ else x i

theorem blockUpdate_add (x : ℕ → ℚ) (w m : ℕ) (y : Fin m → ℚ) (j : Fin m) :
    blockUpdate x w m y (w + j) = y j := by
  simp [blockUpdate]

theorem blockUpdate_of_not_mem (x : ℕ → ℚ) (w m : ℕ) (y : Fin m → ℚ) {i : ℕ}
    (hi : i < w ∨ w + m ≤ i) : blockUpdate x w m y i = x i := by
  unfold blockUpdate
  split_ifs with h
  · omega
  · rfl

/-- **Witness blocks of a call.** If none of `X_w, …, X_{w+m-1}` occurs in the parameter
polynomials, the call has a zero after changing `x` on its block exactly when the callee's
relation holds at `g(x)`. -/
theorem ExPoly.exists_blockUpdate_call_iff {τ : ExPoly} (hτ : τ.WF) (g : Fin τ.params → Poly)
    (w : ℕ) (hg : ∀ k, ∀ i ∈ (g k).vars, i < w ∨ w + τ.witnesses ≤ i) (x : ℕ → ℚ) :
    (∃ y : Fin τ.witnesses → ℚ, ev (blockUpdate x w τ.witnesses y) (τ.call g w) = 0) ↔
      τ.Rel fun k => ev x (g k) := by
  unfold ExPoly.Rel
  refine exists_congr fun y => ?_
  rw [ExPoly.ev_call hτ]
  have h1 : (fun k => ev (blockUpdate x w τ.witnesses y) (g k)) = fun k => ev x (g k) := by
    funext k
    exact ev_congr fun i hi => blockUpdate_of_not_mem x w _ y (hg k i hi)
  have h2 : (fun j : Fin τ.witnesses => blockUpdate x w τ.witnesses y (w + j)) = y := by
    funext j
    exact blockUpdate_add x w _ y j
  rw [h1, h2]

/-- Variables of a call: a variable of `P[g; w]` is a variable of some `g_k` or lies in the
block `[w, w + m)`. -/
theorem mem_vars_callPoly {P : Poly} {p m w : ℕ} (hP : VarsLT P (p + m)) (g : Fin p → Poly)
    {i : ℕ} (hi : i ∈ (callPoly P p w g).vars) :
    (∃ k, i ∈ (g k).vars) ∨ (w ≤ i ∧ i < w + m) := by
  classical
  have := vars_bind₁ (callSubst p w g) P hi
  rw [Finset.mem_biUnion] at this
  obtain ⟨j, hj, hij⟩ := this
  unfold callSubst at hij
  split_ifs at hij with h
  · exact Or.inl ⟨_, hij⟩
  · rw [vars_X, Finset.mem_singleton] at hij
    have := hP j hj
    right
    omega

theorem VarsLT.callPoly {P : Poly} {p m w N : ℕ} (hP : VarsLT P (p + m)) {g : Fin p → Poly}
    (hg : ∀ k, VarsLT (g k) N) (hw : w + m ≤ N) : VarsLT (Syntax.callPoly P p w g) N := by
  intro i hi
  rcases mem_vars_callPoly hP g hi with ⟨k, hk⟩ | ⟨_, h⟩
  · exact hg k i hk
  · omega

theorem ExPoly.varsLT_call {τ : ExPoly} (hτ : τ.WF) {g : Fin τ.params → Poly} {w N : ℕ}
    (hg : ∀ k, VarsLT (g k) N) (hw : w + τ.witnesses ≤ N) : VarsLT (τ.call g w) N :=
  VarsLT.callPoly hτ hg hw

/-! ### Degrees -/

/-- Substitution multiplies the total degree by at most a bound on the substituted
polynomials. -/
theorem totalDegree_bind₁_le {σ τ R : Type*} [CommSemiring R] (f : σ → MvPolynomial τ R)
    (φ : MvPolynomial σ R) (D : ℕ) (h : ∀ i ∈ φ.vars, (f i).totalDegree ≤ D) :
    (bind₁ f φ).totalDegree ≤ φ.totalDegree * D := by
  classical
  conv_lhs => rw [φ.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  calc ∑ i ∈ d.support, (f i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i * D := by
        refine Finset.sum_le_sum fun i hi => (totalDegree_pow _ _).trans ?_
        exact Nat.mul_le_mul_left _ (h i ((mem_vars_iff_mem_support i).2 ⟨d, hd, hi⟩))
    _ = (∑ i ∈ d.support, d i) * D := by rw [Finset.sum_mul]
    _ ≤ φ.totalDegree * D := Nat.mul_le_mul_right _ (le_totalDegree hd)

/-- Degree of a call: at most `deg P · D` when every parameter polynomial has degree at most
`D ≥ 1`. -/
theorem totalDegree_callPoly_le (P : Poly) (p w : ℕ) (g : Fin p → Poly) {D : ℕ} (hD : 1 ≤ D)
    (hg : ∀ k, (g k).totalDegree ≤ D) : (callPoly P p w g).totalDegree ≤ P.totalDegree * D := by
  refine totalDegree_bind₁_le _ _ _ fun i _ => ?_
  unfold callSubst
  split_ifs
  · exact hg _
  · rw [totalDegree_X]
    exact hD

/-- The total degree of a list sum is at most the largest degree of a summand. -/
theorem totalDegree_list_sum_le (l : List Poly) (D : ℕ) (h : ∀ f ∈ l, f.totalDegree ≤ D) :
    l.sum.totalDegree ≤ D := by
  induction l with
  | nil => simp
  | cons f l ih =>
    rw [List.sum_cons]
    exact (totalDegree_add _ _).trans
      (max_le (h f List.mem_cons_self) (ih fun g hg => h g (List.mem_cons_of_mem _ hg)))

/-! ### Renaming into finitely many variables -/

/-- The assignment of `ℕ`-indexed variables extending `v : Fin N → ℚ` by zero. -/
def extendFin {N : ℕ} (v : Fin N → ℚ) (i : ℕ) : ℚ := if h : i < N then v ⟨i, h⟩ else 0

/-- A polynomial whose variables lie below `N` is the renaming of a polynomial in `Fin N`
with the same coefficients (hence the same coefficient bounds), no larger total degree and
the same values. -/
theorem exists_fin_rename {P : Poly} {N : ℕ} (h : VarsLT P N) :
    ∃ Q : MvPolynomial (Fin N) ℤ, rename Fin.val Q = P ∧
      (∀ d, Q.coeff d = P.coeff (d.mapDomain Fin.val)) ∧
      Q.totalDegree ≤ P.totalDegree ∧
      ∀ v : Fin N → ℚ, eval₂ (Int.castRingHom ℚ) v Q = ev (extendFin v) P := by
  obtain ⟨Q, hQ⟩ := exists_rename_eq_of_vars_subset_range P Fin.val Fin.val_injective
    fun i hi => ⟨⟨i, h i hi⟩, rfl⟩
  have hcoeff : ∀ d, Q.coeff d = P.coeff (d.mapDomain Fin.val) := fun d => by
    rw [← hQ, coeff_rename_mapDomain _ Fin.val_injective]
  refine ⟨Q, hQ, hcoeff, ?_, fun v => ?_⟩
  · refine Finset.sup_le fun d hd => ?_
    have hd' : d.mapDomain Fin.val ∈ P.support := by
      rw [mem_support_iff, ← hcoeff]
      exact mem_support_iff.1 hd
    refine le_trans (le_of_eq ?_) (le_totalDegree hd')
    rw [Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)]
  · rw [← hQ, ev_apply, eval₂_rename]
    congr 1
    funext i
    simp [extendFin, i.isLt]

end ZInQ.Syntax
