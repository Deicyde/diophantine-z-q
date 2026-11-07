import ZInQKernel.Compiler.Circuits.RegisterMachine

/-!
# Structured register programs and their compilation

The universal interpreter is a compiled structured program. Its statements are `clear x`,
`inc x`, `pred x` (decrement, no branch), sequencing, `whileDec x body` (while `x` is positive,
decrement it and run `body`), `ifNZ x A B` (decrement-and-restore zero test), `ifLt a b A B`
(the comparison loop that consumes `a` and `b`), `divmod2 y q r` (halving with parity),
labelled loops `loop body` with `brk`, `cont`, and `exit` (a jump to the cleanup stage).
Jumps are `dec J t t` through the reserved jump register `J = 2`, which stays zero.

`Stmt.compile s L ls le ex` lays `s` out at state `L`, with `ls`, `le` the start and end of the
innermost loop and `ex` the exit target. `Exec s ρ o` is the big-step semantics with outcomes
`normal`, `brk`, `cont`, `exit`. `compile_correct` says that the compiled code, placed anywhere
in a machine, runs from its first state to the outcome's target with the outcome's file.

(Blueprint: `compiler/natural/universal/interpreter-primitives.md`, the block framework.)
-/

namespace ZInQ.Compiler.Universal

open RM

/-- The reserved jump register. -/
abbrev J : ℕ := 2

/-- Register files. -/
abbrev Regs : Type := ℕ → ℕ

/-- Structured register programs. -/
inductive Stmt
  | skip
  | clear (x : ℕ)
  | inc (x : ℕ)
  | pred (x : ℕ)
  | seq (s t : Stmt)
  | whileDec (x : ℕ) (body : Stmt)
  | ifNZ (x : ℕ) (s t : Stmt)
  | ifLt (a b : ℕ) (s t : Stmt)
  | divmod2 (y q r : ℕ)
  | loop (body : Stmt)
  | brk
  | cont
  | exit
  deriving Repr

namespace Stmt

/-- The number of instructions of the compiled statement. -/
def size : Stmt → ℕ
  | skip => 0
  | clear _ => 1
  | inc _ => 1
  | pred _ => 1
  | seq s t => s.size + t.size
  | whileDec _ b => b.size + 2
  | ifNZ _ s t => s.size + t.size + 3
  | ifLt _ _ s t => s.size + t.size + 3
  | divmod2 _ _ _ => 8
  | loop b => b.size
  | brk => 1
  | cont => 1
  | exit => 1

/-- Compilation at state `L`, innermost loop `[ls, le)`, exit target `ex`. -/
def compile : Stmt → (L ls le ex : ℕ) → List Instr
  | skip, _, _, _, _ => []
  | clear x, L, _, _, _ => [.dec x L (L + 1)]
  | inc x, L, _, _, _ => [.inc x (L + 1)]
  | pred x, L, _, _, _ => [.dec x (L + 1) (L + 1)]
  | seq s t, L, ls, le, ex => s.compile L ls le ex ++ t.compile (L + s.size) ls le ex
  | whileDec x b, L, ls, le, ex =>
    .dec x (L + 1) (L + b.size + 2) :: b.compile (L + 1) ls le ex ++ [.dec J L L]
  | ifNZ x s t, L, ls, le, ex =>
    .dec x (L + 1) (L + s.size + 3) :: .inc x (L + 2) :: s.compile (L + 2) ls le ex ++
      .dec J (L + s.size + t.size + 3) (L + s.size + t.size + 3) ::
        t.compile (L + s.size + 3) ls le ex
  | ifLt a b s t, L, ls, le, ex =>
    .dec b (L + 1) (L + s.size + 3) :: .dec a L (L + 2) :: s.compile (L + 2) ls le ex ++
      .dec J (L + s.size + t.size + 3) (L + s.size + t.size + 3) ::
        t.compile (L + s.size + 3) ls le ex
  | divmod2 y q r, L, _, _, _ =>
    [.dec y (L + 1) (L + 4), .dec y (L + 2) (L + 6), .inc q (L + 3), .dec J L L,
      .dec r (L + 4) (L + 5), .dec J (L + 8) (L + 8), .dec r (L + 6) (L + 7), .inc r (L + 8)]
  | loop b, L, _, _, ex => b.compile L L (L + b.size) ex
  | brk, _, _, le, _ => [.dec J le le]
  | cont, _, ls, _, _ => [.dec J ls ls]
  | exit, _, _, _, ex => [.dec J ex ex]

theorem length_compile : ∀ (s : Stmt) (L ls le ex : ℕ), (s.compile L ls le ex).length = s.size
  | skip, _, _, _, _ => rfl
  | clear _, _, _, _, _ => rfl
  | inc _, _, _, _, _ => rfl
  | pred _, _, _, _, _ => rfl
  | seq s t, L, ls, le, ex => by
    simp [compile, size, length_compile s, length_compile t]
  | whileDec x b, L, ls, le, ex => by
    simp [compile, size, length_compile b]
  | ifNZ x s t, L, ls, le, ex => by
    simp [compile, size, length_compile s, length_compile t]; omega
  | ifLt a b s t, L, ls, le, ex => by
    simp [compile, size, length_compile s, length_compile t]; omega
  | divmod2 _ _ _, _, _, _, _ => rfl
  | loop b, L, ls, le, ex => by simp [compile, size, length_compile b]
  | brk, _, _, _, _ => rfl
  | cont, _, _, _, _ => rfl
  | exit, _, _, _, _ => rfl

/-- The registers a statement may change. -/
def writes : Stmt → List ℕ
  | skip => []
  | clear x => [x]
  | inc x => [x]
  | pred x => [x]
  | seq s t => s.writes ++ t.writes
  | whileDec x b => x :: b.writes
  | ifNZ _ s t => s.writes ++ t.writes
  | ifLt a b s t => a :: b :: (s.writes ++ t.writes)
  | divmod2 y q r => [y, q, r]
  | loop b => b.writes
  | brk => []
  | cont => []
  | exit => []

/-- Right-nested sequencing of a list of statements. -/
def seqs : List Stmt → Stmt
  | [] => skip
  | s :: ss => seq s (seqs ss)

end Stmt

/-! ### Big-step semantics -/

/-- Outcomes of a statement: normal completion, break, continue, exit to cleanup. -/
inductive Outcome
  | normal (ρ : Regs)
  | brk (ρ : Regs)
  | cont (ρ : Regs)
  | exit (ρ : Regs)

namespace Outcome

/-- The register file of an outcome. -/
def regs : Outcome → Regs
  | normal ρ => ρ
  | brk ρ => ρ
  | cont ρ => ρ
  | exit ρ => ρ

/-- The target state of an outcome, `L` being the end of the statement. -/
def target (L ls le ex : ℕ) : Outcome → ℕ
  | normal _ => L
  | brk _ => le
  | cont _ => ls
  | exit _ => ex

/-- Abnormal outcomes. -/
def IsAbnormal : Outcome → Prop
  | normal _ => False
  | _ => True

end Outcome

open Stmt Outcome

/-- Big-step semantics. Increments of the jump register are excluded, so that it stays zero. -/
inductive Exec : Stmt → Regs → Outcome → Prop
  | skip (ρ) : Exec .skip ρ (.normal ρ)
  | clear (x ρ) : Exec (.clear x) ρ (.normal (Function.update ρ x 0))
  | inc (x ρ) (hx : x ≠ J) : Exec (.inc x) ρ (.normal (Function.update ρ x (ρ x + 1)))
  | pred (x ρ) : Exec (.pred x) ρ (.normal (Function.update ρ x (ρ x - 1)))
  | seq_normal {s t ρ ρ' o} : Exec s ρ (.normal ρ') → Exec t ρ' o → Exec (.seq s t) ρ o
  | seq_abnormal {s t ρ o} : Exec s ρ o → o.IsAbnormal → Exec (.seq s t) ρ o
  | while_zero {x b ρ} : ρ x = 0 → Exec (.whileDec x b) ρ (.normal ρ)
  | while_normal {x b ρ ρ' o} : ρ x ≠ 0 →
      Exec b (Function.update ρ x (ρ x - 1)) (.normal ρ') → Exec (.whileDec x b) ρ' o →
      Exec (.whileDec x b) ρ o
  | while_abnormal {x b ρ o} : ρ x ≠ 0 →
      Exec b (Function.update ρ x (ρ x - 1)) o → o.IsAbnormal → Exec (.whileDec x b) ρ o
  | ifNZ_pos {x s t ρ o} : ρ x ≠ 0 → Exec s ρ o → Exec (.ifNZ x s t) ρ o
  | ifNZ_zero {x s t ρ o} : ρ x = 0 → Exec t ρ o → Exec (.ifNZ x s t) ρ o
  | ifLt_lt {a b s t ρ o} : a ≠ b → ρ a < ρ b →
      Exec s (Function.update (Function.update ρ a 0) b (ρ b - ρ a - 1)) o →
      Exec (.ifLt a b s t) ρ o
  | ifLt_ge {a b s t ρ o} : a ≠ b → ρ b ≤ ρ a →
      Exec t (Function.update (Function.update ρ a (ρ a - ρ b)) b 0) o →
      Exec (.ifLt a b s t) ρ o
  | divmod2 {y q r ρ} : y ≠ q → y ≠ r → q ≠ r → q ≠ J → r ≠ J →
      Exec (.divmod2 y q r) ρ
        (.normal (Function.update (Function.update (Function.update ρ y 0) q (ρ q + ρ y / 2))
          r (ρ y % 2)))
  | loop_normal {b ρ ρ'} : Exec b ρ (.normal ρ') → Exec (.loop b) ρ (.normal ρ')
  | loop_brk {b ρ ρ'} : Exec b ρ (.brk ρ') → Exec (.loop b) ρ (.normal ρ')
  | loop_cont {b ρ ρ' o} : Exec b ρ (.cont ρ') → Exec (.loop b) ρ' o → Exec (.loop b) ρ o
  | loop_exit {b ρ ρ'} : Exec b ρ (.exit ρ') → Exec (.loop b) ρ (.exit ρ')
  | brk (ρ) : Exec .brk ρ (.brk ρ)
  | cont (ρ) : Exec .cont ρ (.cont ρ)
  | exit (ρ) : Exec .exit ρ (.exit ρ)

/-- The jump register stays zero. -/
theorem Exec.regs_J {s : Stmt} {ρ : Regs} {o : Outcome} (h : Exec s ρ o) (hJ : ρ J = 0) :
    o.regs J = 0 := by
  induction h with
  | skip => exact hJ
  | clear x ρ => simp [Outcome.regs, Function.update_apply, hJ]
  | inc x ρ hx => simp [Outcome.regs, hJ, Ne.symm hx]
  | pred x ρ => simp only [Outcome.regs, Function.update_apply]; split_ifs <;> simp_all
  | seq_normal _ _ ih1 ih2 => exact ih2 (ih1 hJ)
  | seq_abnormal _ _ ih => exact ih hJ
  | while_zero _ => exact hJ
  | while_normal _ _ _ ih1 ih2 =>
    refine ih2 (ih1 ?_)
    simp only [Function.update_apply]; split_ifs <;> simp_all
  | while_abnormal _ _ _ ih =>
    refine ih ?_
    simp only [Function.update_apply]; split_ifs <;> simp_all
  | ifNZ_pos _ _ ih => exact ih hJ
  | ifNZ_zero _ _ ih => exact ih hJ
  | ifLt_lt _ _ _ ih =>
    refine ih ?_
    simp only [Function.update_apply]; split_ifs <;> simp_all
  | ifLt_ge _ _ _ ih =>
    refine ih ?_
    simp only [Function.update_apply]; split_ifs <;> simp_all
  | divmod2 _ _ _ hq hr =>
    simp only [Outcome.regs, Function.update_apply, Ne.symm hq, Ne.symm hr, ite_false]
    split_ifs <;> simp_all
  | loop_normal _ ih => exact ih hJ
  | loop_brk _ ih => exact ih hJ
  | loop_cont _ _ ih1 ih2 => exact ih2 (ih1 hJ)
  | loop_exit _ ih => exact ih hJ
  | brk => exact hJ
  | cont => exact hJ
  | exit => exact hJ

/-- A statement leaves every register outside `s.writes` unchanged. -/
theorem Exec.regs_of_not_mem_writes {s : Stmt} {ρ : Regs} {o : Outcome} (h : Exec s ρ o) :
    ∀ k, k ∉ s.writes → o.regs k = ρ k := by
  induction h with
  | skip => intro k _; rfl
  | clear x ρ => intro k hk; simp_all [Stmt.writes, Outcome.regs]
  | inc x ρ _ => intro k hk; simp_all [Stmt.writes, Outcome.regs]
  | pred x ρ => intro k hk; simp_all [Stmt.writes, Outcome.regs]
  | seq_normal _ _ ih1 ih2 =>
    intro k hk
    simp only [Stmt.writes, List.mem_append, not_or] at hk
    rw [ih2 k hk.2]; exact ih1 k hk.1
  | seq_abnormal _ _ ih =>
    intro k hk
    simp only [Stmt.writes, List.mem_append, not_or] at hk
    exact ih k hk.1
  | while_zero _ => intro k _; rfl
  | while_normal _ _ _ ih1 ih2 =>
    intro k hk
    have hk' := hk
    simp only [Stmt.writes, List.mem_cons, not_or] at hk'
    rw [ih2 k hk]
    have := ih1 k hk'.2
    simp only [Outcome.regs] at this
    rw [this, Function.update_of_ne hk'.1]
  | while_abnormal _ _ _ ih =>
    intro k hk
    simp only [Stmt.writes, List.mem_cons, not_or] at hk
    rw [ih k hk.2, Function.update_of_ne hk.1]
  | ifNZ_pos _ _ ih =>
    intro k hk
    simp only [Stmt.writes, List.mem_append, not_or] at hk
    exact ih k hk.1
  | ifNZ_zero _ _ ih =>
    intro k hk
    simp only [Stmt.writes, List.mem_append, not_or] at hk
    exact ih k hk.2
  | ifLt_lt _ _ _ ih =>
    intro k hk
    simp only [Stmt.writes, List.mem_cons, List.mem_append, not_or] at hk
    rw [ih k hk.2.2.1, Function.update_of_ne hk.2.1, Function.update_of_ne hk.1]
  | ifLt_ge _ _ _ ih =>
    intro k hk
    simp only [Stmt.writes, List.mem_cons, List.mem_append, not_or] at hk
    rw [ih k hk.2.2.2, Function.update_of_ne hk.2.1, Function.update_of_ne hk.1]
  | divmod2 =>
    intro k hk
    simp only [Stmt.writes, List.mem_cons, List.not_mem_nil, or_false, not_or] at hk
    simp [Outcome.regs, Function.update_of_ne hk.1, Function.update_of_ne hk.2.1,
      Function.update_of_ne hk.2.2]
  | loop_normal _ ih => exact ih
  | loop_brk _ ih => exact ih
  | loop_cont _ _ ih1 ih2 => intro k hk; rw [ih2 k hk]; exact ih1 k hk
  | loop_exit _ ih => exact ih
  | brk => intro k _; rfl
  | cont => intro k _; rfl
  | exit => intro k _; rfl

/-! ### Runs of machines -/

/-- `c'` is reachable from `c` in finitely many steps. -/
def Reaches (μ : Machine) (c c' : Config) : Prop := ∃ t, stepN μ t c = some c'

theorem Reaches.refl (μ : Machine) (c : Config) : Reaches μ c c := ⟨0, rfl⟩

theorem Reaches.trans {μ : Machine} {c₁ c₂ c₃ : Config} (h₁ : Reaches μ c₁ c₂)
    (h₂ : Reaches μ c₂ c₃) : Reaches μ c₁ c₃ := by
  obtain ⟨t₁, h₁⟩ := h₁
  obtain ⟨t₂, h₂⟩ := h₂
  exact ⟨t₁ + t₂, by rw [stepN_add, h₁]; exact h₂⟩

theorem Reaches.of_step {μ : Machine} {c c' : Config} (h : step μ c = some c') :
    Reaches μ c c' := ⟨1, by rw [stepN_succ, h]; rfl⟩

/-- The code `cd` sits at state `L` of the machine `μ`. -/
def CodeAt (μ : Machine) (L : ℕ) (cd : List Instr) : Prop :=
  ∀ k (h : k < cd.length), μ (L + k) = cd[k]

theorem CodeAt.append_left {μ : Machine} {L : ℕ} {cd d : List Instr} (h : CodeAt μ L (cd ++ d)) :
    CodeAt μ L cd := fun k hk => by
  rw [h k (by simp; omega), List.getElem_append_left hk]

theorem CodeAt.append_right {μ : Machine} {L : ℕ} {cd d : List Instr} (h : CodeAt μ L (cd ++ d)) :
    CodeAt μ (L + cd.length) d := fun k hk => by
  rw [Nat.add_assoc, h (cd.length + k) (by simp; omega),
    List.getElem_append_right (by omega)]
  simp

theorem CodeAt.cons_head {μ : Machine} {L : ℕ} {i : Instr} {cd : List Instr}
    (h : CodeAt μ L (i :: cd)) : μ L = i := h 0 (by simp)

theorem CodeAt.cons_tail {μ : Machine} {L : ℕ} {i : Instr} {cd : List Instr}
    (h : CodeAt μ L (i :: cd)) : CodeAt μ (L + 1) cd := fun k hk => by
  rw [Nat.add_assoc, Nat.add_comm 1 k, h (k + 1) (by simp; omega)]
  simp

theorem CodeAt.get {μ : Machine} {L : ℕ} {cd : List Instr} (h : CodeAt μ L cd) (k : ℕ)
    (hk : k < cd.length) : μ (L + k) = cd[k] := h k hk

theorem reaches_inc {μ : Machine} {L j x : ℕ} {ρ : Regs} (h : μ L = .inc j x) :
    Reaches μ ⟨L, ρ⟩ ⟨x, Function.update ρ j (ρ j + 1)⟩ :=
  Reaches.of_step (by simp [step, h])

theorem reaches_dec_pos {μ : Machine} {L j x y : ℕ} {ρ : Regs} (h : μ L = .dec j x y)
    (hj : ρ j ≠ 0) : Reaches μ ⟨L, ρ⟩ ⟨x, Function.update ρ j (ρ j - 1)⟩ :=
  Reaches.of_step (by simp [step, h, hj])

theorem reaches_dec_zero {μ : Machine} {L j x y : ℕ} {ρ : Regs} (h : μ L = .dec j x y)
    (hj : ρ j = 0) : Reaches μ ⟨L, ρ⟩ ⟨y, ρ⟩ :=
  Reaches.of_step (by simp [step, h, hj])

theorem reaches_jump {μ : Machine} {L x : ℕ} {ρ : Regs} (h : μ L = .dec J x x) (hJ : ρ J = 0) :
    Reaches μ ⟨L, ρ⟩ ⟨x, ρ⟩ := reaches_dec_zero h hJ

/-- A self-loop `dec x L (L + 1)` clears `x`. -/
theorem reaches_clear {μ : Machine} {L x : ℕ} (h : μ L = .dec x L (L + 1)) :
    ∀ ρ : Regs, Reaches μ ⟨L, ρ⟩ ⟨L + 1, Function.update ρ x 0⟩ := by
  suffices ∀ n (ρ : Regs), ρ x = n → Reaches μ ⟨L, ρ⟩ ⟨L + 1, Function.update ρ x 0⟩ from
    fun ρ => this _ ρ rfl
  intro n
  induction n with
  | zero =>
    intro ρ hρ
    rw [Function.update_eq_self_iff.mpr hρ.symm]
    exact reaches_dec_zero h hρ
  | succ n ih =>
    intro ρ hρ
    refine (reaches_dec_pos h (by omega)).trans ?_
    have := ih (Function.update ρ x (ρ x - 1)) (by simp; omega)
    simpa using this

/-- The comparison loop `dec b (L+1) E; dec a L (L+2)`. -/
theorem reaches_ifLt {μ : Machine} {L a b E : ℕ} (hab : a ≠ b) (h0 : μ L = .dec b (L + 1) E)
    (h1 : μ (L + 1) = .dec a L (L + 2)) :
    ∀ ρ : Regs,
      (ρ a < ρ b →
        Reaches μ ⟨L, ρ⟩ ⟨L + 2, Function.update (Function.update ρ a 0) b (ρ b - ρ a - 1)⟩) ∧
      (ρ b ≤ ρ a →
        Reaches μ ⟨L, ρ⟩ ⟨E, Function.update (Function.update ρ a (ρ a - ρ b)) b 0⟩) := by
  suffices ∀ n (ρ : Regs), ρ a = n →
      (ρ a < ρ b →
        Reaches μ ⟨L, ρ⟩ ⟨L + 2, Function.update (Function.update ρ a 0) b (ρ b - ρ a - 1)⟩) ∧
      (ρ b ≤ ρ a →
        Reaches μ ⟨L, ρ⟩ ⟨E, Function.update (Function.update ρ a (ρ a - ρ b)) b 0⟩) from
    fun ρ => this _ ρ rfl
  intro n
  induction n with
  | zero =>
    intro ρ hρ
    refine ⟨fun hlt => ?_, fun hle => ?_⟩
    · refine (reaches_dec_pos h0 (by omega)).trans ?_
      have := reaches_dec_zero (ρ := Function.update ρ b (ρ b - 1)) h1
        (by rw [Function.update_of_ne hab]; exact hρ)
      convert this using 2
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    · have : ρ b = 0 := by omega
      convert reaches_dec_zero h0 this using 2
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all
  | succ n ih =>
    intro ρ hρ
    refine ⟨fun hlt => ?_, fun hle => ?_⟩
    · have step1 := reaches_dec_pos (ρ := ρ) h0 (by omega)
      have step2 := reaches_dec_pos (ρ := Function.update ρ b (ρ b - 1)) h1
        (by rw [Function.update_of_ne hab]; omega)
      set ρ' := Function.update (Function.update ρ b (ρ b - 1)) a
        (Function.update ρ b (ρ b - 1) a - 1) with hρ'
      have ha' : ρ' a = n := by simp [hρ', Function.update_of_ne hab]; omega
      have hb' : ρ' b = ρ b - 1 := by simp [hρ', Function.update_of_ne (Ne.symm hab)]
      have := (ih ρ' ha').1 (by omega)
      refine step1.trans (step2.trans ?_)
      convert this using 2
      funext k
      simp only [hρ', Function.update_apply]
      split_ifs <;> simp_all
      omega
    · by_cases hb : ρ b = 0
      · convert reaches_dec_zero h0 hb using 2
        funext k
        simp only [Function.update_apply]
        split_ifs <;> simp_all
      have step1 := reaches_dec_pos (ρ := ρ) h0 hb
      have step2 := reaches_dec_pos (ρ := Function.update ρ b (ρ b - 1)) h1
        (by rw [Function.update_of_ne hab]; omega)
      set ρ' := Function.update (Function.update ρ b (ρ b - 1)) a
        (Function.update ρ b (ρ b - 1) a - 1) with hρ'
      have ha' : ρ' a = n := by simp [hρ', Function.update_of_ne hab]; omega
      have hb' : ρ' b = ρ b - 1 := by simp [hρ', Function.update_of_ne (Ne.symm hab)]
      have := (ih ρ' ha').2 (by omega)
      refine step1.trans (step2.trans ?_)
      convert this using 2
      funext k
      simp only [hρ', Function.update_apply]
      split_ifs <;> simp_all
      omega

/-- The halving loop of `divmod2`. -/
theorem reaches_divmod2 {μ : Machine} {L y q r : ℕ} (hyq : y ≠ q) (hqJ : q ≠ J) (hrJ : r ≠ J)
    (hcode : CodeAt μ L ((Stmt.divmod2 y q r).compile L 0 0 0)) :
    ∀ ρ : Regs, ρ J = 0 →
      Reaches μ ⟨L, ρ⟩ ⟨L + 8, Function.update (Function.update (Function.update ρ y 0) q
        (ρ q + ρ y / 2)) r (ρ y % 2)⟩ := by
  have h0 : μ L = .dec y (L + 1) (L + 4) := hcode.get 0 (by simp [Stmt.compile])
  have h1 : μ (L + 1) = .dec y (L + 2) (L + 6) := hcode.get 1 (by simp [Stmt.compile])
  have h2 : μ (L + 2) = .inc q (L + 3) := hcode.get 2 (by simp [Stmt.compile])
  have h3 : μ (L + 3) = .dec J L L := hcode.get 3 (by simp [Stmt.compile])
  have h4 : μ (L + 4) = .dec r (L + 4) (L + 4 + 1) := hcode.get 4 (by simp [Stmt.compile])
  have h5 : μ (L + 5) = .dec J (L + 8) (L + 8) := hcode.get 5 (by simp [Stmt.compile])
  have h6 : μ (L + 6) = .dec r (L + 6) (L + 6 + 1) := hcode.get 6 (by simp [Stmt.compile])
  have h7 : μ (L + 7) = .inc r (L + 8) := hcode.get 7 (by simp [Stmt.compile])
  suffices ∀ n (ρ : Regs), ρ y = n → ρ J = 0 →
      Reaches μ ⟨L, ρ⟩ ⟨L + 8, Function.update (Function.update (Function.update ρ y 0) q
        (ρ q + ρ y / 2)) r (ρ y % 2)⟩ from fun ρ => this _ ρ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro ρ hy hJ
    rcases n with _ | _ | n
    · refine (reaches_dec_zero h0 hy).trans ((reaches_clear h4 ρ).trans ?_)
      have := reaches_jump (ρ := Function.update ρ r 0) h5 (by
        rw [Function.update_apply]; split_ifs <;> simp_all)
      convert this using 2
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    · refine (reaches_dec_pos h0 (by omega)).trans ?_
      refine (reaches_dec_zero h1 (by simp [hy])).trans ?_
      refine (reaches_clear h6 _).trans ?_
      refine (reaches_inc h7).trans ?_
      convert Reaches.refl μ _ using 2
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    · refine (reaches_dec_pos h0 (by omega)).trans ?_
      refine (reaches_dec_pos h1 (by simp [hy])).trans ?_
      refine (reaches_inc h2).trans ?_
      refine (reaches_jump h3 (by
        simp only [Function.update_apply]; split_ifs <;> simp_all)).trans ?_
      refine (ih n (by omega) _ (by simp [Function.update_apply, hyq, hy]) (by
        simp only [Function.update_apply]; split_ifs <;> simp_all)).trans ?_
      convert Reaches.refl μ _ using 2
      funext k
      have : (n + 2) / 2 = n / 2 + 1 := by omega
      have h2' : (n + 2) % 2 = n % 2 := by omega
      simp only [Function.update_apply]
      split_ifs <;> simp_all <;> omega

/-! ### Correctness of the compilation -/

theorem CodeAt.seq {μ : Machine} {L ls le ex : ℕ} {s t : Stmt}
    (h : CodeAt μ L ((Stmt.seq s t).compile L ls le ex)) :
    CodeAt μ L (s.compile L ls le ex) ∧
      CodeAt μ (L + s.size) (t.compile (L + s.size) ls le ex) := by
  simp only [Stmt.compile] at h
  refine ⟨h.append_left, ?_⟩
  have := h.append_right
  rwa [Stmt.length_compile] at this

theorem CodeAt.whileDec {μ : Machine} {L ls le ex x : ℕ} {b : Stmt}
    (h : CodeAt μ L ((Stmt.whileDec x b).compile L ls le ex)) :
    μ L = .dec x (L + 1) (L + b.size + 2) ∧ CodeAt μ (L + 1) (b.compile (L + 1) ls le ex) ∧
      μ (L + 1 + b.size) = .dec J L L := by
  simp only [Stmt.compile] at h
  refine ⟨h.cons_head, h.cons_tail.append_left, ?_⟩
  have := h.cons_tail.append_right
  rw [Stmt.length_compile] at this
  exact this.cons_head

theorem CodeAt.ifNZ {μ : Machine} {L ls le ex x : ℕ} {s t : Stmt}
    (h : CodeAt μ L ((Stmt.ifNZ x s t).compile L ls le ex)) :
    μ L = .dec x (L + 1) (L + s.size + 3) ∧ μ (L + 1) = .inc x (L + 2) ∧
      CodeAt μ (L + 2) (s.compile (L + 2) ls le ex) ∧
      μ (L + 2 + s.size) = .dec J (L + s.size + t.size + 3) (L + s.size + t.size + 3) ∧
      CodeAt μ (L + s.size + 3) (t.compile (L + s.size + 3) ls le ex) := by
  simp only [Stmt.compile] at h
  have h2 := h.cons_tail.cons_tail
  have h3 := h2.append_right
  rw [Stmt.length_compile] at h3
  refine ⟨h.cons_head, h.cons_tail.cons_head, h2.append_left, h3.cons_head, ?_⟩
  have := h3.cons_tail
  rwa [show L + 1 + 1 + s.size + 1 = L + s.size + 3 by omega] at this

theorem CodeAt.ifLt {μ : Machine} {L ls le ex a b : ℕ} {s t : Stmt}
    (h : CodeAt μ L ((Stmt.ifLt a b s t).compile L ls le ex)) :
    μ L = .dec b (L + 1) (L + s.size + 3) ∧ μ (L + 1) = .dec a L (L + 2) ∧
      CodeAt μ (L + 2) (s.compile (L + 2) ls le ex) ∧
      μ (L + 2 + s.size) = .dec J (L + s.size + t.size + 3) (L + s.size + t.size + 3) ∧
      CodeAt μ (L + s.size + 3) (t.compile (L + s.size + 3) ls le ex) := by
  simp only [Stmt.compile] at h
  have h2 := h.cons_tail.cons_tail
  have h3 := h2.append_right
  rw [Stmt.length_compile] at h3
  refine ⟨h.cons_head, h.cons_tail.cons_head, h2.append_left, h3.cons_head, ?_⟩
  have := h3.cons_tail
  rwa [show L + 1 + 1 + s.size + 1 = L + s.size + 3 by omega] at this

/-- **Correctness of the compilation.** The compiled code of `s`, placed at state `L` of any
machine, runs from `L` to the target of the outcome with the outcome's register file. -/
theorem compile_correct {μ : Machine} {s : Stmt} {ρ : Regs} {o : Outcome} (hexec : Exec s ρ o) :
    ∀ {L ls le ex : ℕ}, CodeAt μ L (s.compile L ls le ex) → ρ J = 0 →
      Reaches μ ⟨L, ρ⟩ ⟨o.target (L + s.size) ls le ex, o.regs⟩ := by
  induction hexec with
  | skip ρ => intro L ls le ex _ _; exact Reaches.refl _ _
  | clear x ρ =>
    intro L ls le ex h _
    exact reaches_clear (h.get 0 (by simp [Stmt.compile])) ρ
  | inc x ρ _ =>
    intro L ls le ex h _
    exact reaches_inc (h.get 0 (by simp [Stmt.compile]))
  | pred x ρ =>
    intro L ls le ex h _
    have h0 : μ L = .dec x (L + 1) (L + 1) := h.get 0 (by simp [Stmt.compile])
    by_cases hx : ρ x = 0
    · have := reaches_dec_zero (ρ := ρ) h0 hx
      simp only [Outcome.target, Outcome.regs, Stmt.size]
      rwa [show ρ x - 1 = ρ x by omega, Function.update_eq_self]
    · exact reaches_dec_pos h0 hx
  | seq_normal h1 h2 ih1 ih2 =>
    intro L ls le ex h hJ
    obtain ⟨hs, ht⟩ := h.seq
    have := ih2 ht (h1.regs_J hJ)
    rw [Stmt.size, ← Nat.add_assoc]
    exact (ih1 hs hJ).trans this
  | @seq_abnormal s t ρ o h1 hab ih =>
    intro L ls le ex h hJ
    obtain ⟨hs, -⟩ := h.seq
    have := ih hs hJ
    cases o <;> simp_all [Outcome.target, Outcome.IsAbnormal]
  | @while_zero x b ρ hx =>
    intro L ls le ex h hJ
    obtain ⟨h0, -, -⟩ := h.whileDec
    have := reaches_dec_zero (ρ := ρ) h0 hx
    simpa [Outcome.target, Outcome.regs, Stmt.size, Nat.add_assoc] using this
  | @while_normal x b ρ ρ' o hx hb hw ihb ihw =>
    intro L ls le ex h hJ
    obtain ⟨h0, hbody, hjump⟩ := h.whileDec
    have hJ1 : Function.update ρ x (ρ x - 1) J = 0 := by
      simp only [Function.update_apply]; split_ifs <;> simp_all
    have hJ' := hb.regs_J hJ1
    refine (reaches_dec_pos h0 hx).trans ((ihb hbody hJ1).trans ?_)
    exact (reaches_jump hjump hJ').trans (ihw h hJ')
  | @while_abnormal x b ρ o hx hb hab ihb =>
    intro L ls le ex h hJ
    obtain ⟨h0, hbody, -⟩ := h.whileDec
    have hJ1 : Function.update ρ x (ρ x - 1) J = 0 := by
      simp only [Function.update_apply]; split_ifs <;> simp_all
    refine (reaches_dec_pos h0 hx).trans ?_
    have := ihb hbody hJ1
    cases o <;> simp_all [Outcome.target, Outcome.IsAbnormal]
  | @ifNZ_pos x s t ρ o hx hs ih =>
    intro L ls le ex h hJ
    obtain ⟨h0, h1, hcs, hj, -⟩ := h.ifNZ
    refine (reaches_dec_pos h0 hx).trans ?_
    refine (reaches_inc h1).trans ?_
    have e : Function.update (Function.update ρ x (ρ x - 1)) x
        (Function.update ρ x (ρ x - 1) x + 1) = ρ := by
      funext k; simp only [Function.update_apply]; split_ifs <;> simp_all; omega
    rw [e]
    refine (ih hcs hJ).trans ?_
    cases o with
    | normal ρ' =>
      have := reaches_jump (ρ := ρ') hj (hs.regs_J hJ)
      simpa [Outcome.target, Outcome.regs, Stmt.size, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using this
    | _ => exact Reaches.refl _ _
  | @ifNZ_zero x s t ρ o hx ht ih =>
    intro L ls le ex h hJ
    obtain ⟨h0, -, -, -, hct⟩ := h.ifNZ
    refine (reaches_dec_zero h0 hx).trans ?_
    have := ih hct hJ
    cases o <;> simpa [Outcome.target, Stmt.size, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using this
  | @ifLt_lt a b s t ρ o hab hlt hs ih =>
    intro L ls le ex h hJ
    obtain ⟨h0, h1, hcs, hj, -⟩ := h.ifLt
    refine ((reaches_ifLt hab h0 h1 ρ).1 hlt).trans ?_
    have hJ1 : Function.update (Function.update ρ a 0) b (ρ b - ρ a - 1) J = 0 := by
      simp only [Function.update_apply]; split_ifs <;> simp_all
    refine (ih hcs hJ1).trans ?_
    cases o with
    | normal ρ' =>
      have := reaches_jump (ρ := ρ') hj (hs.regs_J hJ1)
      simpa [Outcome.target, Outcome.regs, Stmt.size, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using this
    | _ => exact Reaches.refl _ _
  | @ifLt_ge a b s t ρ o hab hge ht ih =>
    intro L ls le ex h hJ
    obtain ⟨h0, h1, -, -, hct⟩ := h.ifLt
    refine ((reaches_ifLt hab h0 h1 ρ).2 hge).trans ?_
    have hJ1 : Function.update (Function.update ρ a (ρ a - ρ b)) b 0 J = 0 := by
      simp only [Function.update_apply]; split_ifs <;> simp_all
    have := ih hct hJ1
    cases o <;> simpa [Outcome.target, Stmt.size, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using this
  | @divmod2 y q r ρ hyq _ _ hqJ hrJ =>
    intro L ls le ex h hJ
    have hcode : CodeAt μ L ((Stmt.divmod2 y q r).compile L 0 0 0) := h
    exact reaches_divmod2 hyq hqJ hrJ hcode ρ hJ
  | @loop_normal b ρ ρ' hb ih =>
    intro L ls le ex h hJ
    exact ih (ls := L) (le := L + b.size) h hJ
  | @loop_brk b ρ ρ' hb ih =>
    intro L ls le ex h hJ
    exact ih (ls := L) (le := L + b.size) h hJ
  | @loop_cont b ρ ρ' o hb hl ihb ihl =>
    intro L ls le ex h hJ
    exact (ihb (ls := L) (le := L + b.size) h hJ).trans (ihl h (hb.regs_J hJ))
  | @loop_exit b ρ ρ' hb ih =>
    intro L ls le ex h hJ
    exact ih (ls := L) (le := L + b.size) h hJ
  | brk ρ =>
    intro L ls le ex h hJ
    exact reaches_jump (h.get 0 (by simp [Stmt.compile])) hJ
  | cont ρ =>
    intro L ls le ex h hJ
    exact reaches_jump (h.get 0 (by simp [Stmt.compile])) hJ
  | exit ρ =>
    intro L ls le ex h hJ
    exact reaches_jump (h.get 0 (by simp [Stmt.compile])) hJ

end ZInQ.Compiler.Universal
