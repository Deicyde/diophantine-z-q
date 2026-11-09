import ZInQKernel.Syntax.Templates.Scope

/-!
# Template constructions allocate from one counter

Blueprint: `syntax/language/formula-compilation.md`, `syntax/language/builder-soundness.md`.

Templates are built by programs of the state monad `Build` (`ZInQKernel.Syntax.Language.Build`):
the state is the allocation counter and the list of global equations `q X_c ≐ u` of the rational
constants. The template of a construction `b` with `p` parameters is, by definition
(`Build.template`), the existential polynomial with `p` parameters, `v - p` witnesses and
polynomial `κ(⋀(E_1, …, E_r, φ))`, where `φ`, `E_1, …, E_r` and `v` are the final formula,
global equations and counter of `b` run from `(p, [])`. There is no node encoding: the
polynomial is the compiled formula itself.

`Build` is a shallow embedding, so a program may in principle modify its state arbitrarily.
`Build.Allocates b` says that `b` uses the state only as a counter: from every state the counter
does not decrease and the only new global equations are for newly allocated variables, in
increasing order. Every primitive of the construction language allocates and allocation is
closed under `bind` (`Build.Allocates.bind`), so every construction written with them does.
For such constructions `Build.template_construction` gives the parameter and variable counts,
the polynomial, the ranges of the constant variables and well-formedness from the final formula
alone.
-/

namespace ZInQ.Syntax

open MvPolynomial

namespace Build

/-- `b` *allocates*: run from any state it does not decrease the counter, and it only appends
global equations whose variables are newly allocated (at or above the initial counter, below
the final one), in increasing order. -/
def Allocates {α : Type} (b : Build α) : Prop :=
  ∀ s : BuildState, s.next ≤ (b s).2.next ∧ ∃ l : List (ℕ × ℤ × ℤ),
    (b s).2.globals = s.globals ++ l ∧ (l.map Prod.fst).Pairwise (· < ·) ∧
      ∀ e ∈ l, s.next ≤ e.1 ∧ e.1 < (b s).2.next

namespace Allocates

variable {α β γ : Type}

/-- A program that only advances the counter allocates. -/
theorem of_next {b : Build α}
    (h : ∀ s : BuildState, s.next ≤ (b s).2.next ∧ (b s).2.globals = s.globals) :
    Allocates b :=
  fun s => ⟨(h s).1, [], by simp [(h s).2]⟩

theorem pure (a : α) : Allocates (Pure.pure a : Build α) :=
  of_next fun _ => ⟨le_rfl, rfl⟩

theorem bind {b : Build α} {f : α → Build β} (hb : Allocates b) (hf : ∀ a, Allocates (f a)) :
    Allocates (b >>= f) := by
  intro s
  obtain ⟨h1, l1, hg1, hp1, hr1⟩ := hb s
  obtain ⟨h2, l2, hg2, hp2, hr2⟩ := hf (b s).1 (b s).2
  simp only [bind_apply]
  refine ⟨h1.trans h2, l1 ++ l2, by rw [hg2, hg1, List.append_assoc], ?_, fun e he => ?_⟩
  · rw [List.map_append, List.pairwise_append]
    refine ⟨hp1, hp2, fun i hi j hj => ?_⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hi
    obtain ⟨e', he', rfl⟩ := List.mem_map.1 hj
    exact lt_of_lt_of_le (hr1 e he).2 (hr2 e' he').1
  · rcases List.mem_append.1 he with he | he
    · exact ⟨(hr1 e he).1, lt_of_lt_of_le (hr1 e he).2 h2⟩
    · exact ⟨h1.trans (hr2 e he).1, (hr2 e he).2⟩

theorem fresh : Allocates Build.fresh := of_next fun _ => ⟨Nat.le_succ _, rfl⟩

theorem freshIdx : Allocates Build.freshIdx := of_next fun _ => ⟨Nat.le_succ _, rfl⟩

theorem call (τ : ExPoly) (g : Fin τ.params → Poly) : Allocates (Build.call τ g) :=
  of_next fun _ => ⟨Nat.le_add_right _ _, rfl⟩

theorem nz (a : Poly) : Allocates (Build.nz a) := of_next fun _ => ⟨Nat.le_succ _, rfl⟩

theorem pos (a : Poly) : Allocates (Build.pos a) :=
  bind fresh fun _ => bind fresh fun _ => bind fresh fun _ => bind fresh fun _ => pure _

theorem fnz (u : Pair) : Allocates (Build.fnz u) := nz _

theorem fdiv (n d : Pair) : Allocates (Build.fdiv n d) :=
  bind fresh fun _ => bind fresh fun _ => bind (fnz d) fun _ => pure _

theorem zGadget (p : Code) (ζ : Pair) : Allocates (Build.zGadget p ζ) :=
  bind (fnz _) fun _ => pure _

theorem freshPoint : Allocates Build.freshPoint :=
  bind fresh fun _ => bind fresh fun _ => bind fresh fun _ => bind fresh fun _ =>
    bind fresh fun _ => pure _

theorem freshPair : Allocates Build.freshPair := bind fresh fun _ => bind fresh fun _ => pure _

theorem point : Allocates Build.point := of_next fun _ => ⟨Nat.le_add_right _ _, rfl⟩

theorem freshPoints (n : ℕ) : Allocates (Build.freshPoints n) :=
  of_next fun _ => ⟨Nat.le_add_right _ _, rfl⟩

theorem freshPairs (n : ℕ) : Allocates (Build.freshPairs n) :=
  of_next fun _ => ⟨Nat.le_add_right _ _, rfl⟩

/-- A rational constant allocates: it returns a constant, an already recorded variable, or a
new variable `X_c` with the new global equation for `c`. -/
theorem rational (u q : ℤ) : Allocates (Build.rational u q) := by
  intro s
  unfold Build.rational
  dsimp only
  split_ifs
  · exact ⟨le_rfl, [], by simp⟩
  · split
    · exact ⟨le_rfl, [], by simp⟩
    · exact ⟨Nat.le_succ _, [(s.next, normalize u q)], rfl, by simp, by simp⟩

theorem gen : Allocates Build.gen :=
  bind (rational _ _) fun _ => bind (rational _ _) fun _ => bind (rational _ _) fun _ => pure _

theorem mapL {f : γ → Build α} (hf : ∀ a, Allocates (f a)) (l : List γ) :
    Allocates (Build.mapL f l) := by
  induction l with
  | nil => exact pure _
  | cons a l ih =>
    rw [Build.mapL_cons]
    exact bind (hf a) fun _ => bind ih fun _ => pure _

end Allocates

end Build

/-- The template of a construction, unfolded: `p` parameters, `v - p` witnesses and polynomial
`κ(⋀(E_1, …, E_r, φ))`. -/
theorem Build.template_eq (p : ℕ) (b : Build Formula) :
    Build.template p b = ⟨p, (b ⟨p, []⟩).2.next - p, (Build.fullFormula p b).compile⟩ := rfl

/-- **Template construction from formulas.** Let a construction `b` with `p` parameters allocate,
and let it end with formula `φ`, global equations `E_1, …, E_r` and counter `v`. Then its template
has parameter count `p`, variable count `v` and polynomial `κ(⋀(E_1, …, E_r, φ))`; the variables
of the global equations are pairwise distinct (increasing) and lie in `[p, v)`; and the template
is well formed (every variable of its polynomial lies below `v`) as soon as every variable of
`κ(φ)` does. -/
theorem Build.template_construction (p : ℕ) {b : Build Formula} (hb : b.Allocates) :
    (Build.template p b).params = p ∧
      (Build.template p b).varCount = (b ⟨p, []⟩).2.next ∧
      (Build.template p b).poly = (Build.fullFormula p b).compile ∧
      ((b ⟨p, []⟩).2.globals.map Prod.fst).Pairwise (· < ·) ∧
      (∀ e ∈ (b ⟨p, []⟩).2.globals, p ≤ e.1 ∧ e.1 < (b ⟨p, []⟩).2.next) ∧
      (VarsLT (b ⟨p, []⟩).1.compile (b ⟨p, []⟩).2.next → (Build.template p b).WF) := by
  obtain ⟨hp, l, hl, hpw, hr⟩ := hb ⟨p, []⟩
  simp only [List.nil_append] at hl
  rw [hl]
  refine ⟨rfl, Build.template_varCount p b hp, rfl, hpw, hr, fun hφ => ?_⟩
  exact Build.template_wf p b hp (fun e he => (hr e (hl ▸ he)).2) hφ

end ZInQ.Syntax
