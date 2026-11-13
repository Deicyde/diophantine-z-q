import ZInQKernel.Syntax.Language.Basic

/-!
# Formulas and their polynomial compilation

A formula is built from atoms `a ≐ b`, `⟨f⟩` and call atoms `⟨τ[g; w]⟩` by n-ary conjunction
and disjunction. Its compilation `κ` sends `a ≐ b` to `a - b`, `⟨f⟩` to `f`, a call atom to the
call polynomial, a conjunction to the sum of the squares of the compiled conjuncts and a
disjunction to the product of the compiled disjuncts (empty sum `0`, empty product `1`).
No flattening takes place.

The main theorem `Formula.ev_compile_eq_zero_iff` says that over `ℚ` the compiled polynomial
vanishes exactly when the formula holds. The call atom is a tagged form of `⟨f⟩` that keeps
the callee, its parameter polynomials and its witness start, so that private witness blocks
can be tracked (see `ZInQKernel.Syntax.Language.Lifting`).
-/

namespace ZInQ.Syntax

open MvPolynomial

/-- Formulas over `ℤ[X_i : i ∈ ℕ]`. -/
inductive Formula
  /-- The atom `a ≐ b`. -/
  | eq (a b : Poly)
  /-- The atom `⟨f⟩`, read as `f = 0`. -/
  | atom (f : Poly)
  /-- The call atom `⟨τ[g; w]⟩`. -/
  | call (τ : ExPoly) (g : Fin τ.params → Poly) (w : ℕ)
  /-- The conjunction `⋀ (φ_1, …, φ_k)`. -/
  | and (fs : List Formula)
  /-- The disjunction `⋁ (φ_1, …, φ_k)`. -/
  | or (fs : List Formula)

namespace Formula

/-- Induction on formulas with the hypothesis for every member of a conjunction or a
disjunction. -/
@[elab_as_elim]
theorem induct' {P : Formula → Prop} (eq : ∀ a b, P (.eq a b)) (atom : ∀ f, P (.atom f))
    (call : ∀ τ g w, P (.call τ g w)) (and : ∀ fs, (∀ φ ∈ fs, P φ) → P (.and fs))
    (or : ∀ fs, (∀ φ ∈ fs, P φ) → P (.or fs)) (φ : Formula) : P φ :=
  Formula.rec (motive_1 := P) (motive_2 := fun fs => ∀ φ ∈ fs, P φ) eq atom call and or
    (fun _ h => absurd h List.not_mem_nil)
    (fun _ _ hh ht => List.forall_mem_cons.2 ⟨hh, ht⟩) φ

/-- The compilation `κ`. -/
noncomputable def compile : Formula → Poly
  | .eq a b => a - b
  | .atom f => f
  | .call τ g w => τ.call g w
  | .and fs => (fs.map fun φ => φ.compile ^ 2).sum
  | .or fs => (fs.map fun φ => φ.compile).prod

/-- Truth of a formula at a rational assignment. -/
def Holds (x : ℕ → ℚ) : Formula → Prop
  | .eq a b => ev x a = ev x b
  | .atom f => ev x f = 0
  | .call τ g w => ev x (τ.call g w) = 0
  | .and fs => ∀ φ, (_ : φ ∈ fs) → Holds x φ
  | .or fs => ∃ φ, ∃ (_ : φ ∈ fs), Holds x φ
decreasing_by all_goals (have := List.sizeOf_lt_of_mem ‹_ ∈ fs›; simp; omega)

@[simp] theorem compile_eq (a b : Poly) : (Formula.eq a b).compile = a - b := by
  simp [compile]

@[simp] theorem compile_atom (f : Poly) : (Formula.atom f).compile = f := by simp [compile]

@[simp] theorem compile_call (τ : ExPoly) (g : Fin τ.params → Poly) (w : ℕ) :
    (Formula.call τ g w).compile = τ.call g w := by simp [compile]

theorem compile_and (fs : List Formula) :
    (Formula.and fs).compile = (fs.map fun φ => φ.compile ^ 2).sum := by
  simp [compile]

theorem compile_or (fs : List Formula) :
    (Formula.or fs).compile = (fs.map fun φ => φ.compile).prod := by
  simp [compile]

@[simp] theorem holds_eq (x : ℕ → ℚ) (a b : Poly) :
    (Formula.eq a b).Holds x ↔ ev x a = ev x b := by simp [Holds]

@[simp] theorem holds_atom (x : ℕ → ℚ) (f : Poly) : (Formula.atom f).Holds x ↔ ev x f = 0 := by
  simp [Holds]

@[simp] theorem holds_call (x : ℕ → ℚ) (τ : ExPoly) (g : Fin τ.params → Poly) (w : ℕ) :
    (Formula.call τ g w).Holds x ↔ ev x (τ.call g w) = 0 := by simp [Holds]

@[simp] theorem holds_and (x : ℕ → ℚ) (fs : List Formula) :
    (Formula.and fs).Holds x ↔ ∀ φ ∈ fs, φ.Holds x := by
  rw [Holds]

@[simp] theorem holds_or (x : ℕ → ℚ) (fs : List Formula) :
    (Formula.or fs).Holds x ↔ ∃ φ ∈ fs, φ.Holds x := by
  rw [Holds]
  exact ⟨fun ⟨φ, hφ, h⟩ => ⟨φ, hφ, h⟩, fun ⟨φ, hφ, h⟩ => ⟨φ, hφ, h⟩⟩

end Formula

/-! ### Sums of squares and products over the rationals -/

theorem ev_sum_sq_nonneg (x : ℕ → ℚ) (l : List Poly) : 0 ≤ ev x (l.map (· ^ 2)).sum := by
  induction l with
  | nil => simp
  | cons f l ih =>
    rw [List.map_cons, List.sum_cons, map_add, map_pow]
    exact add_nonneg (sq_nonneg _) ih

/-- Over `ℚ` a finite sum of squares vanishes exactly when every term vanishes. -/
theorem ev_sum_sq_eq_zero_iff (x : ℕ → ℚ) (l : List Poly) :
    ev x (l.map (· ^ 2)).sum = 0 ↔ ∀ f ∈ l, ev x f = 0 := by
  induction l with
  | nil => simp
  | cons f l ih =>
    rw [List.map_cons, List.sum_cons, map_add, map_pow,
      add_eq_zero_iff_of_nonneg (sq_nonneg _) (ev_sum_sq_nonneg x l), ih, List.forall_mem_cons,
      pow_eq_zero_iff two_ne_zero]

/-- Over `ℚ` a finite product vanishes exactly when some factor vanishes. -/
theorem ev_prod_eq_zero_iff (x : ℕ → ℚ) (l : List Poly) :
    ev x l.prod = 0 ↔ ∃ f ∈ l, ev x f = 0 := by
  rw [map_list_prod, List.prod_eq_zero_iff, List.mem_map]

namespace Formula

/-- **Sums of squares and products over the rationals.** For every formula `φ` and every
`x : ℕ → ℚ`, `κ(φ)(x) = 0` exactly when `φ` holds at `x`. -/
theorem ev_compile_eq_zero_iff (φ : Formula) (x : ℕ → ℚ) : ev x φ.compile = 0 ↔ φ.Holds x := by
  induction φ using Formula.induct' with
  | eq a b => simp [sub_eq_zero]
  | atom f => simp
  | call τ g w => simp
  | and fs ih =>
    rw [compile_and, holds_and]
    have : (fs.map fun φ => φ.compile ^ 2) = (fs.map compile).map (· ^ 2) := by
      rw [List.map_map]; rfl
    rw [this, ev_sum_sq_eq_zero_iff]
    simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    exact forall₂_congr fun φ hφ => ih φ hφ
  | or fs ih =>
    rw [compile_or, holds_or, ev_prod_eq_zero_iff]
    simp only [List.mem_map, exists_exists_and_eq_and]
    exact exists_congr fun φ => and_congr_right fun hφ => ih φ hφ

/-- A formula holds at `x` exactly when it holds at any `y` agreeing with `x` on the variables
of its compilation. -/
theorem holds_congr {φ : Formula} {x y : ℕ → ℚ} (h : ∀ i ∈ φ.compile.vars, x i = y i) :
    φ.Holds x ↔ φ.Holds y := by
  rw [← ev_compile_eq_zero_iff, ← ev_compile_eq_zero_iff, ev_congr h]

/-! ### Atoms, variable ranges and degrees -/

/-- The compiled atoms of a formula (`a - b`, `f` and call polynomials). -/
noncomputable def atoms : Formula → List Poly
  | .eq a b => [a - b]
  | .atom f => [f]
  | .call τ g w => [τ.call g w]
  | .and fs => fs.flatMap fun φ => φ.atoms
  | .or fs => fs.flatMap fun φ => φ.atoms

@[simp] theorem atoms_and (fs : List Formula) : (Formula.and fs).atoms = fs.flatMap atoms := by
  rw [atoms]

@[simp] theorem atoms_or (fs : List Formula) : (Formula.or fs).atoms = fs.flatMap atoms := by
  rw [atoms]

/-- If every compiled atom has its variables below `N`, so has the compilation. -/
theorem varsLT_compile {φ : Formula} {N : ℕ} (h : ∀ f ∈ φ.atoms, VarsLT f N) :
    VarsLT φ.compile N := by
  induction φ using Formula.induct' with
  | eq a b => simpa [atoms] using h
  | atom f => simpa [atoms] using h
  | call τ g w => simpa [atoms] using h
  | and fs ih =>
    rw [compile_and]
    refine VarsLT.list_sum fun f hf => ?_
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hf
    exact (ih φ hφ fun f hf => h f (by simpa using ⟨φ, hφ, hf⟩)).pow 2
  | or fs ih =>
    rw [compile_or]
    refine VarsLT.list_prod fun f hf => ?_
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hf
    exact ih φ hφ fun f hf => h f (by simpa using ⟨φ, hφ, hf⟩)

/-- A degree bound computed from the formula: the degree of an atom, twice the largest
degree of a conjunct, the sum of the degrees of the disjuncts. -/
noncomputable def degree : Formula → ℕ
  | .eq a b => max a.totalDegree b.totalDegree
  | .atom f => f.totalDegree
  | .call τ g w => (τ.call g w).totalDegree
  | .and fs => 2 * (fs.map fun φ => φ.degree).foldr max 0
  | .or fs => (fs.map fun φ => φ.degree).sum

/-- Degree of a conjunction: at most twice a bound on the conjuncts. -/
theorem totalDegree_compile_and_le (fs : List Formula) (D : ℕ)
    (h : ∀ φ ∈ fs, φ.compile.totalDegree ≤ D) : (Formula.and fs).compile.totalDegree ≤ 2 * D := by
  rw [compile_and]
  refine totalDegree_list_sum_le _ _ fun f hf => ?_
  obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hf
  refine (totalDegree_pow _ _).trans ?_
  exact Nat.mul_le_mul_left 2 (h φ hφ)

/-- Degree of a disjunction: at most the sum of the degrees of the disjuncts. -/
theorem totalDegree_compile_or_le (fs : List Formula) :
    (Formula.or fs).compile.totalDegree ≤ (fs.map fun φ => φ.compile.totalDegree).sum := by
  rw [compile_or]
  refine (totalDegree_list_prod _).trans (le_of_eq ?_)
  rw [List.map_map]
  rfl

theorem le_foldr_max {l : List ℕ} {a : ℕ} (h : a ∈ l) : a ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons b l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- The total degree of a compiled formula is at most `Formula.degree`. -/
theorem totalDegree_compile_le (φ : Formula) : φ.compile.totalDegree ≤ φ.degree := by
  induction φ using Formula.induct' with
  | eq a b => simpa [degree] using totalDegree_sub a b
  | atom f => simp [degree]
  | call τ g w => simp [degree]
  | and fs ih =>
    rw [degree]
    refine totalDegree_compile_and_le fs _ fun φ hφ => (ih φ hφ).trans ?_
    exact le_foldr_max (List.mem_map_of_mem hφ)
  | or fs ih =>
    rw [degree]
    refine (totalDegree_compile_or_le fs).trans ?_
    induction fs with
    | nil => simp
    | cons φ fs ihfs =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (ih φ List.mem_cons_self)
        (ihfs fun ψ hψ => ih ψ (List.mem_cons_of_mem _ hψ))

end Formula

/-! ### The sum-of-squares and product combinators on polynomials -/

/-- Degree of a sum of squares of polynomials of degree at most `D`. -/
theorem totalDegree_sum_sq_le (l : List Poly) (D : ℕ) (h : ∀ f ∈ l, f.totalDegree ≤ D) :
    (l.map (· ^ 2)).sum.totalDegree ≤ 2 * D := by
  refine totalDegree_list_sum_le _ _ fun f hf => ?_
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
  exact (totalDegree_pow _ _).trans (Nat.mul_le_mul_left 2 (h g hg))

theorem VarsLT.sum_sq {l : List Poly} {N : ℕ} (h : ∀ f ∈ l, VarsLT f N) :
    VarsLT (l.map (· ^ 2)).sum N := by
  refine VarsLT.list_sum fun f hf => ?_
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf
  exact (h g hg).pow 2

end ZInQ.Syntax
