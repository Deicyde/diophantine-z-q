import ZInQKernel.Syntax.Language.Lifting
import ZInQKernel.Syntax.Language.Gadgets

/-!
# Template constructions

A construction of a template with `p` parameters keeps a counter `c`, initially `p`; the
parameters are `X_0, …, X_{p-1}`. It may take a fresh variable `X_c`, call an existential
polynomial on a fresh block `X_c, …, X_{c+m-1}`, or request a rational constant `u/q`: the
first request takes a fresh variable `X_c` and records the global equation `q X_c ≐ u`, later
requests return the same variable, and an integer constant (`q = 1`) is the polynomial `u`.
If the construction ends with formula `φ`, global equations `E_1, …, E_r` and counter `v`, the
template has parameter count `p`, witness count `v - p` and polynomial
`κ(⋀(E_1, …, E_r, φ))`.

Constructions are programs in the state monad `Build`. The gadgets `NZ(a)` (one fresh `w`,
the atom `a w ≐ 1`) and `POS(a)` (four fresh `z_i`, the atom `a (z_1² + ⋯ + z_4²) ≐ 1`) are
defined here with their semantics.
-/

namespace ZInQ.Syntax

open MvPolynomial

/-- The state of a construction: the counter and the recorded global equations
`(c, u, q)`, meaning `q X_c ≐ u`, in order of creation. -/
structure BuildState where
  /-- The next free variable. -/
  next : ℕ
  /-- The global equations of the rational constants. -/
  globals : List (ℕ × ℤ × ℤ)

/-- Template constructions. -/
def Build (α : Type) : Type := BuildState → α × BuildState

namespace Build

instance : Monad Build where
  pure a s := (a, s)
  bind m f s := f (m s).1 (m s).2

@[simp] theorem pure_apply {α : Type} (a : α) (s : BuildState) : (pure a : Build α) s = (a, s) :=
  rfl

@[simp] theorem bind_apply {α β : Type} (m : Build α) (f : α → Build β) (s : BuildState) :
    (m >>= f) s = f (m s).1 (m s).2 := rfl

/-- A fresh variable index. -/
def freshIdx : Build ℕ := fun s => (s.next, { s with next := s.next + 1 })

/-- A fresh variable. -/
noncomputable def fresh : Build Poly := fun s => (X s.next, { s with next := s.next + 1 })

/-- The call of `τ` on the parameter polynomials `g`, on a fresh block. -/
noncomputable def call (τ : ExPoly) (g : Fin τ.params → Poly) : Build Formula :=
  fun s => (.call τ g s.next, { s with next := s.next + τ.witnesses })

/-- Sign normalization of a rational constant `u/q`. -/
def normalize (u q : ℤ) : ℤ × ℤ := if q < 0 then (-u, -q) else (u, q)

/-- The rational constant `u/q`. -/
noncomputable def rational (u q : ℤ) : Build Poly := fun s =>
  let k := normalize u q
  if k.2 = 1 then (C k.1, s) else
    match s.globals.find? (fun e => e.2 == k) with
    | some e => (X e.1, s)
    | none => (X s.next, ⟨s.next + 1, s.globals ++ [(s.next, k)]⟩)

@[simp] theorem freshIdx_apply (s : BuildState) :
    freshIdx s = (s.next, { s with next := s.next + 1 }) := rfl

@[simp] theorem fresh_apply (s : BuildState) :
    fresh s = (X s.next, { s with next := s.next + 1 }) := rfl

@[simp] theorem call_apply (τ : ExPoly) (g : Fin τ.params → Poly) (s : BuildState) :
    call τ g s = (.call τ g s.next, { s with next := s.next + τ.witnesses }) := rfl

/-- The first request of a rational constant `u/q`, `q ≥ 2`. -/
theorem rational_apply_new {u q : ℤ} (hq : 2 ≤ q) (s : BuildState)
    (hs : ∀ e ∈ s.globals, e.2 ≠ (u, q)) :
    rational u q s = (X s.next, ⟨s.next + 1, s.globals ++ [(s.next, u, q)]⟩) := by
  have hn : normalize u q = (u, q) := by simp [normalize]; omega
  have hfind : s.globals.find? (fun e => e.2 == (u, q)) = none := by
    rw [List.find?_eq_none]
    intro e he
    simpa using hs e he
  simp only [rational, hn]
  rw [ite_eq_right (by omega), hfind]

/-- A repeated request of a rational constant returns the same variable. -/
theorem rational_apply_old {u q : ℤ} (hq : 2 ≤ q) (s : BuildState) {c : ℕ}
    (hs : s.globals.find? (fun e => e.2 == (u, q)) = some (c, u, q)) :
    rational u q s = (X c, s) := by
  have hn : normalize u q = (u, q) := by simp [normalize]; omega
  simp only [rational, hn]
  rw [ite_eq_right (by omega), hs]

/-- An integer constant is the constant polynomial. -/
theorem rational_apply_one (u : ℤ) (s : BuildState) : rational u 1 s = (C u, s) := by
  simp [rational, normalize]

end Build

/-- The global equation `q X_c ≐ u`. -/
noncomputable def globalEq (e : ℕ × ℤ × ℤ) : Formula := .eq (C e.2.2 * X e.1) (C e.2.1)

/-- The template constructed by a program with `p` parameters. -/
noncomputable def Build.template (p : ℕ) (b : Build Formula) : ExPoly :=
  ⟨p, (b ⟨p, []⟩).2.next - p,
    (Formula.and ((b ⟨p, []⟩).2.globals.map globalEq ++ [(b ⟨p, []⟩).1])).compile⟩

/-! ### Rational constants by global equations -/

theorem holds_globalEq (x : ℕ → ℚ) (e : ℕ × ℤ × ℤ) (hq : e.2.2 ≠ 0) :
    (globalEq e).Holds x ↔ x e.1 = e.2.1 / e.2.2 := by
  rw [globalEq, Formula.holds_eq, eq_div_iff (by exact_mod_cast hq)]
  simp [mul_comm]

/-- **Rational constants by global equations.** The polynomial `κ(⋀(E_1, …, E_r, φ))` vanishes
at `x` exactly when every constant variable takes its value and `φ` holds at `x`. -/
theorem ev_globals_eq_zero_iff (eqs : List (ℕ × ℤ × ℤ)) (hq : ∀ e ∈ eqs, e.2.2 ≠ 0)
    (φ : Formula) (x : ℕ → ℚ) :
    ev x (Formula.and (eqs.map globalEq ++ [φ])).compile = 0 ↔
      (∀ e ∈ eqs, x e.1 = e.2.1 / e.2.2) ∧ φ.Holds x := by
  rw [Formula.ev_compile_eq_zero_iff, Formula.holds_and, List.forall_mem_append,
    List.forall_mem_singleton, List.forall_mem_map]
  exact and_congr_left' (forall₂_congr fun e he => holds_globalEq x e (hq e he))

/-- A template without rational constants has polynomial `κ(φ)²`. -/
theorem compile_globals_nil (φ : Formula) :
    (Formula.and (([] : List (ℕ × ℤ × ℤ)).map globalEq ++ [φ])).compile = φ.compile ^ 2 := by
  simp [Formula.compile_and]

/-- The generator constants: `8 g₀ = 1641`, `4 g₁ = -15465`, `32 g₂ = 87483` hold exactly at
`(1641/8, -15465/4, 87483/32)`. -/
theorem generator_values (g0 g1 g2 : ℚ) :
    (8 * g0 = 1641 ∧ 4 * g1 = -15465 ∧ 32 * g2 = 87483) ↔
      (g0 = 1641 / 8 ∧ g1 = -15465 / 4 ∧ g2 = 87483 / 32) := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

/-! ### Relations of constructed templates -/

/-- For a well-formed existential polynomial, the relation is the existence of a full
assignment extending the parameters. -/
theorem ExPoly.rel_iff_exists_assignment {τ : ExPoly} (hτ : τ.WF) (a : Fin τ.params → ℚ) :
    τ.Rel a ↔ ∃ y : ℕ → ℚ, (∀ i : Fin τ.params, y i = a i) ∧ ev y τ.poly = 0 := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨_, fun i => assign_of_lt a y i.isLt, hy⟩
  · rintro ⟨y, hya, hy⟩
    refine ⟨fun j => y (τ.params + j), ?_⟩
    rw [← hy]
    refine ev_congr fun i hi => ?_
    have := hτ i hi
    unfold assign
    split_ifs with h1 h2
    · exact (hya ⟨i, h1⟩).symm
    · show y (τ.params + (i - τ.params)) = y i
      rw [Nat.add_sub_cancel' (by omega)]
    · unfold ExPoly.varCount at this; omega

/-- **Relations through private blocks.** If the polynomial of `τ` is the compilation of a
scoped formula `φ` whose blocks lie above the parameters, then `Rel_τ(a)` holds exactly when
`φ^*` holds at some assignment extending `a` (the block variables are irrelevant there, by
`Formula.lift_congr`). -/
theorem ExPoly.rel_iff_exists_lift {τ : ExPoly} (hτ : τ.WF) {φ : Formula}
    (hpoly : τ.poly = φ.compile) (hφ : φ.Scoped) (hblocks : ∀ b ∈ φ.blocks, τ.params ≤ b.1)
    (a : Fin τ.params → ℚ) :
    τ.Rel a ↔ ∃ y : ℕ → ℚ, (∀ i : Fin τ.params, y i = a i) ∧ φ.Lift y := by
  rw [ExPoly.rel_iff_exists_assignment hτ, hpoly]
  simp only [Formula.ev_compile_eq_zero_iff]
  constructor
  · rintro ⟨y, hya, hy⟩
    exact ⟨y, hya, (Formula.exists_holds_iff φ hφ y).1 ⟨y, fun _ _ => rfl, hy⟩⟩
  · rintro ⟨y, hya, hy⟩
    obtain ⟨y', hy', h⟩ := (Formula.exists_holds_iff φ hφ y).2 hy
    refine ⟨y', fun i => ?_, h⟩
    rw [hy' i, hya i]
    rintro ⟨b, hb, hib, -⟩
    have := hblocks b hb
    have := i.isLt
    omega

/-- The relation of a constructed template: some values of the witnesses satisfy the global
equations and the final formula. -/
theorem Build.template_rel_iff (p : ℕ) (b : Build Formula)
    (hq : ∀ e ∈ (b ⟨p, []⟩).2.globals, e.2.2 ≠ 0) (a : Fin p → ℚ) :
    (Build.template p b).Rel a ↔
      ∃ y : Fin ((b ⟨p, []⟩).2.next - p) → ℚ,
        (∀ e ∈ (b ⟨p, []⟩).2.globals, assign p _ a y e.1 = e.2.1 / e.2.2) ∧
          (b ⟨p, []⟩).1.Holds (assign p _ a y) := by
  unfold ExPoly.Rel Build.template
  exact exists_congr fun y => ev_globals_eq_zero_iff _ hq _ _

/-- The variable count of a constructed template is its final counter. -/
theorem Build.template_varCount (p : ℕ) (b : Build Formula) (hp : p ≤ (b ⟨p, []⟩).2.next) :
    (Build.template p b).varCount = (b ⟨p, []⟩).2.next := by
  simp only [ExPoly.varCount, Build.template]
  omega

theorem varsLT_compile_globals {eqs : List (ℕ × ℤ × ℤ)} {φ : Formula} {N : ℕ}
    (hg : ∀ e ∈ eqs, e.1 < N) (hφ : VarsLT φ.compile N) :
    VarsLT (Formula.and (eqs.map globalEq ++ [φ])).compile N := by
  rw [Formula.compile_and]
  refine VarsLT.list_sum fun f hf => ?_
  obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.1 hf
  refine VarsLT.pow ?_ 2
  rcases List.mem_append.1 hψ with h | h
  · obtain ⟨e, he, rfl⟩ := List.mem_map.1 h
    simp only [globalEq, Formula.compile_eq]
    exact ((VarsLT.C _ _).mul (VarsLT.X (hg e he))).sub (VarsLT.C _ _)
  · rw [List.mem_singleton] at h
    exact h ▸ hφ

/-- A constructed template is well formed when its final formula and its constant variables
lie below the final counter. -/
theorem Build.template_wf (p : ℕ) (b : Build Formula) (hp : p ≤ (b ⟨p, []⟩).2.next)
    (hg : ∀ e ∈ (b ⟨p, []⟩).2.globals, e.1 < (b ⟨p, []⟩).2.next)
    (hφ : VarsLT (b ⟨p, []⟩).1.compile (b ⟨p, []⟩).2.next) : (Build.template p b).WF := by
  unfold ExPoly.WF
  rw [Build.template_varCount p b hp]
  exact varsLT_compile_globals hg hφ

theorem totalDegree_compile_globals_le {eqs : List (ℕ × ℤ × ℤ)} {φ : Formula} {D : ℕ}
    (hD : 1 ≤ D) (hφ : φ.compile.totalDegree ≤ D) :
    (Formula.and (eqs.map globalEq ++ [φ])).compile.totalDegree ≤ 2 * D := by
  refine Formula.totalDegree_compile_and_le _ _ fun ψ hψ => ?_
  rcases List.mem_append.1 hψ with h | h
  · obtain ⟨e, -, rfl⟩ := List.mem_map.1 h
    simp only [globalEq, Formula.compile_eq]
    refine (totalDegree_sub _ _).trans (max_le ((totalDegree_mul _ _).trans ?_) ?_)
    · simp only [totalDegree_C, totalDegree_X, zero_add]
      exact hD
    · exact (totalDegree_C _).le.trans (Nat.zero_le _)
  · rw [List.mem_singleton] at h
    exact h ▸ hφ

/-- Degree of a constructed template: at most twice a bound `D ≥ 1` on its final formula. -/
theorem Build.totalDegree_template_le (p : ℕ) (b : Build Formula) {D : ℕ} (hD : 1 ≤ D)
    (hφ : (b ⟨p, []⟩).1.compile.totalDegree ≤ D) :
    (Build.template p b).poly.totalDegree ≤ 2 * D :=
  totalDegree_compile_globals_le hD hφ

/-! ### The gadgets `NZ` and `POS` -/

/-- The atom `a X_c ≐ 1` of `NZ(a)` with fresh variable `X_c`. -/
noncomputable def nzFormula (a : Poly) (c : ℕ) : Formula := .eq (a * X c) 1

/-- The atom `a (X_c² + X_{c+1}² + X_{c+2}² + X_{c+3}²) ≐ 1` of `POS(a)`. -/
noncomputable def posFormula (a : Poly) (c : ℕ) : Formula :=
  .eq (a * (X c ^ 2 + X (c + 1) ^ 2 + X (c + 2) ^ 2 + X (c + 3) ^ 2)) 1

/-- `NZ(a)`: one fresh variable `w` and the atom `a w ≐ 1`. -/
noncomputable def Build.nz (a : Poly) : Build Formula := do
  let w ← Build.fresh
  pure (.eq (a * w) 1)

/-- `POS(a)`: four fresh variables `z_i` and the atom `a (z_1² + z_2² + z_3² + z_4²) ≐ 1`. -/
noncomputable def Build.pos (a : Poly) : Build Formula := do
  let z1 ← Build.fresh
  let z2 ← Build.fresh
  let z3 ← Build.fresh
  let z4 ← Build.fresh
  pure (.eq (a * (z1 ^ 2 + z2 ^ 2 + z3 ^ 2 + z4 ^ 2)) 1)

@[simp] theorem Build.nz_apply (a : Poly) (s : BuildState) :
    Build.nz a s = (nzFormula a s.next, { s with next := s.next + 1 }) := rfl

@[simp] theorem Build.pos_apply (a : Poly) (s : BuildState) :
    Build.pos a s = (posFormula a s.next, { s with next := s.next + 4 }) := rfl

theorem holds_nzFormula (x : ℕ → ℚ) (a : Poly) (c : ℕ) :
    (nzFormula a c).Holds x ↔ ev x a * x c = 1 := by
  simp [nzFormula]

theorem lift_nzFormula (y : ℕ → ℚ) (a : Poly) (c : ℕ) :
    (nzFormula a c).Lift y ↔ ev y a * y c = 1 := by
  simp [nzFormula]

/-- **Inverse witnesses.** `NZ(a)` is satisfiable by a choice of its fresh variable exactly
when `a ≠ 0`, and the fresh variable is then `1/a`. -/
theorem exists_update_nzFormula_iff (x : ℕ → ℚ) (a : Poly) {c : ℕ} (hc : c ∉ a.vars) :
    (∃ t : ℚ, (nzFormula a c).Holds (Function.update x c t)) ↔ ev x a ≠ 0 := by
  have ha : ∀ t, ev (Function.update x c t) a = ev x a := fun t =>
    ev_congr fun i hi => Function.update_of_ne (by rintro rfl; exact hc hi) _ _
  simp only [holds_nzFormula, ha, Function.update_self]
  exact exists_mul_eq_one_iff _

theorem holds_posFormula (x : ℕ → ℚ) (a : Poly) (c : ℕ) :
    (posFormula a c).Holds x ↔
      ev x a * (x c ^ 2 + x (c + 1) ^ 2 + x (c + 2) ^ 2 + x (c + 3) ^ 2) = 1 := by
  simp [posFormula]

/-- **Strict positivity.** `POS(a)` is satisfiable by a choice of its four fresh variables
exactly when `a > 0`. -/
theorem exists_blockUpdate_posFormula_iff (x : ℕ → ℚ) (a : Poly) {c : ℕ}
    (hc : ∀ i ∈ a.vars, i < c ∨ c + 4 ≤ i) :
    (∃ z : Fin 4 → ℚ, (posFormula a c).Holds (blockUpdate x c 4 z)) ↔ 0 < ev x a := by
  have ha : ∀ z, ev (blockUpdate x c 4 z) a = ev x a := fun z =>
    ev_congr fun i hi => blockUpdate_of_not_mem x c 4 z (hc i hi)
  have hz : ∀ (z : Fin 4 → ℚ) (j : Fin 4), blockUpdate x c 4 z (c + j) = z j :=
    fun z j => blockUpdate_add x c 4 z j
  rw [pos_iff_four_squares]
  refine exists_congr fun z => ?_
  rw [holds_posFormula, ha]
  have h0 := hz z 0
  have h1 := hz z 1
  have h2 := hz z 2
  have h3 := hz z 3
  simp only [Fin.val_zero, add_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  have h3' : blockUpdate x c 4 z (c + 3) = z 3 := h3
  rw [h0, h1, h2, h3']

end ZInQ.Syntax
