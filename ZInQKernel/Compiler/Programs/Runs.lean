import ZInQKernel.Compiler.Programs.IR

/-!
# Runs of register machines

Small-step facts used by the correctness of the lowering: reachability `Reaches`, the step
of each instruction, the embedding of an instruction list into a machine at an offset, and
the generic loops `clear` (one self-looping decrement) and `transfer` (move a register into
one or two others, the jump register being zero).
-/

namespace ZInQ.Compiler.IR

open RM

/-- `d` is reached from `c` in exactly `n` steps. -/
def ReachesIn (μ : Machine) (n : ℕ) (c d : Config) : Prop := stepN μ n c = some d

/-- `d` is reached from `c` after finitely many steps. -/
def Reaches (μ : Machine) (c d : Config) : Prop := ∃ n, ReachesIn μ n c d

theorem Reaches.refl (μ : Machine) (c : Config) : Reaches μ c c := ⟨0, rfl⟩

theorem ReachesIn.trans {μ : Machine} {m n : ℕ} {c d e : Config} (h₁ : ReachesIn μ m c d)
    (h₂ : ReachesIn μ n d e) : ReachesIn μ (m + n) c e := by
  unfold ReachesIn at *; rw [stepN_add, h₁]; exact h₂

theorem Reaches.trans {μ : Machine} {c d e : Config} (h₁ : Reaches μ c d) (h₂ : Reaches μ d e) :
    Reaches μ c e := by
  obtain ⟨m, hm⟩ := h₁; obtain ⟨n, hn⟩ := h₂; exact ⟨m + n, hm.trans hn⟩

theorem ReachesIn.of_step {μ : Machine} {n : ℕ} {c d e : Config} (h : step μ c = some d)
    (h' : ReachesIn μ n d e) : ReachesIn μ (n + 1) c e := by
  unfold ReachesIn at *; rw [stepN_succ, h]; exact h'

theorem Reaches.of_step {μ : Machine} {c d e : Config} (h : step μ c = some d)
    (h' : Reaches μ d e) : Reaches μ c e := by
  obtain ⟨n, hn⟩ := h'; exact ⟨n + 1, hn.of_step h⟩

/-- A run reaching `d` in `n` steps, with `n ≥ 1`. -/
theorem Reaches.of_step_pos {μ : Machine} {c d e : Config} (h : step μ c = some d)
    (h' : Reaches μ d e) : ∃ n, 0 < n ∧ ReachesIn μ n c e := by
  obtain ⟨n, hn⟩ := h'; exact ⟨n + 1, by omega, hn.of_step h⟩

theorem step_inc {μ : Machine} {s j x : ℕ} {σ : ℕ → ℕ} (h : μ s = .inc j x) :
    step μ ⟨s, σ⟩ = some ⟨x, Function.update σ j (σ j + 1)⟩ := by
  simp [step, h]

theorem step_dec_pos {μ : Machine} {s j x y : ℕ} {σ : ℕ → ℕ} (h : μ s = .dec j x y)
    (hj : σ j ≠ 0) : step μ ⟨s, σ⟩ = some ⟨x, Function.update σ j (σ j - 1)⟩ := by
  simp [step, h, hj]

theorem step_dec_zero {μ : Machine} {s j x y : ℕ} {σ : ℕ → ℕ} (h : μ s = .dec j x y)
    (hj : σ j = 0) : step μ ⟨s, σ⟩ = some ⟨y, σ⟩ := by
  simp [step, h, hj]

/-- After a halting configuration nothing is reached. -/
theorem stepN_eq_none_of_halt {μ : Machine} {c : Config} (h : μ c.state = .halt) (n : ℕ) :
    stepN μ (n + 1) c = none := by
  rw [stepN_succ, (step_eq_none_iff μ c).mpr h]; rfl

/-- Determinism: if the run from `c` halts at time `t` and reaches `d` at time `k`, then
`k ≤ t` and the run from `d` halts at time `t - k`. -/
theorem halts_after {μ : Machine} {c d h : Config} {k t : ℕ} (hk : ReachesIn μ k c d)
    (ht : ReachesIn μ t c h) (hh : μ h.state = .halt) : k ≤ t ∧ ReachesIn μ (t - k) d h := by
  by_cases hkt : k ≤ t
  · refine ⟨hkt, ?_⟩
    have := ht
    unfold ReachesIn at this hk ⊢
    rw [show t = k + (t - k) by omega, stepN_add, hk] at this
    exact this
  · exfalso
    unfold ReachesIn at hk ht
    have e : k = t + (k - t - 1 + 1) := by omega
    rw [e, stepN_add, ht, Option.bind_some, stepN_eq_none_of_halt hh] at hk
    cases hk

/-! ### Embedding an instruction list -/

/-- The list `l` sits in the machine `μ` from state `s` on. -/
def Embedded (μ : Machine) (s : ℕ) (l : List Instr) : Prop :=
  ∀ i (h : i < l.length), μ (s + i) = l[i]

theorem Embedded.append_left {μ : Machine} {s : ℕ} {l₁ l₂ : List Instr}
    (h : Embedded μ s (l₁ ++ l₂)) : Embedded μ s l₁ := fun i hi => by
  rw [h i (by simp; omega), List.getElem_append_left hi]

theorem Embedded.append_right {μ : Machine} {s : ℕ} {l₁ l₂ : List Instr}
    (h : Embedded μ s (l₁ ++ l₂)) : Embedded μ (s + l₁.length) l₂ := fun i hi => by
  rw [Nat.add_assoc, h (l₁.length + i) (by simp; omega), List.getElem_append_right (by omega)]
  simp

theorem Embedded.head {μ : Machine} {s : ℕ} {a : Instr} {l : List Instr}
    (h : Embedded μ s (a :: l)) : μ s = a := h 0 (by simp)

theorem Embedded.tail {μ : Machine} {s : ℕ} {a : Instr} {l : List Instr}
    (h : Embedded μ s (a :: l)) : Embedded μ (s + 1) l := fun i hi => by
  rw [Nat.add_assoc, Nat.add_comm 1 i, h (i + 1) (by simp; omega)]; simp

theorem Embedded.get {μ : Machine} {s : ℕ} {l : List Instr} (h : Embedded μ s l) {i : ℕ}
    (hi : i < l.length) {a : Instr} (ha : l[i] = a) : μ (s + i) = a := by
  rw [h i hi, ha]

/-- An instruction list embedded at `0` in the machine of a program extending it. -/
theorem embedded_toMachine (l l' : List Instr) : Embedded (RM.Program.toMachine (l ++ l')) 0 l := by
  intro i hi
  rw [toMachine_of_lt _ (by simp; omega)]
  simp only [Nat.zero_add]
  exact List.getElem_append_left hi

theorem embedded_toMachine_append (l₀ l l' : List Instr) :
    Embedded (RM.Program.toMachine (l₀ ++ l ++ l')) l₀.length l := by
  intro i hi
  have hlt : l₀.length + i < (l₀ ++ l ++ l').length := by simp; omega
  rw [toMachine_of_lt _ hlt]
  simp [List.getElem_append_right, List.getElem_append_left, hi]

/-! ### Clearing and transferring loops -/

/-- The jump through a register `J` that holds zero. -/
def jmp (J x : ℕ) : Instr := .dec J x x

theorem step_jmp {μ : Machine} {s J x : ℕ} {σ : ℕ → ℕ} (h : μ s = jmp J x) (hJ : σ J = 0) :
    step μ ⟨s, σ⟩ = some ⟨x, σ⟩ := step_dec_zero h hJ

/-- `clear x`: the self-loop `dec x s (s+1)`. -/
theorem reachesIn_clear {μ : Machine} {s x : ℕ} (h : μ s = .dec x s (s + 1)) (σ : ℕ → ℕ) :
    ReachesIn μ (σ x + 1) ⟨s, σ⟩ ⟨s + 1, Function.update σ x 0⟩ := by
  induction hx : σ x generalizing σ with
  | zero =>
    have : Function.update σ x 0 = σ := by rw [← hx]; exact Function.update_eq_self x σ
    rw [this]; exact ReachesIn.of_step (step_dec_zero h hx) rfl
  | succ n ih =>
    have h1 := step_dec_pos h (σ := σ) (by omega)
    have h2 := ih (Function.update σ x (σ x - 1)) (by simp; omega)
    rw [Function.update_idem] at h2
    exact h2.of_step h1

theorem reaches_clear {μ : Machine} {s x : ℕ} (h : μ s = .dec x s (s + 1)) (σ : ℕ → ℕ) :
    Reaches μ ⟨s, σ⟩ ⟨s + 1, Function.update σ x 0⟩ := ⟨_, reachesIn_clear h σ⟩

/-- `transfer y d`: move `y` into `d` (`dec y`, `inc d`, jump back). -/
theorem reaches_transfer1 {μ : Machine} {s J y d : ℕ} (h0 : μ s = .dec y (s + 1) (s + 3))
    (h1 : μ (s + 1) = .inc d (s + 2)) (h2 : μ (s + 2) = jmp J s) (hyd : y ≠ d) (hJy : J ≠ y)
    (hJd : J ≠ d) (σ : ℕ → ℕ) (hJ : σ J = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + 3, fun i => if i = y then 0 else if i = d then σ d + σ y else σ i⟩ := by
  induction hy : σ y generalizing σ with
  | zero =>
    have : (fun i => if i = y then 0 else if i = d then σ d + 0 else σ i) = σ := by
      funext i; split_ifs with h1 h2 <;> subst_vars <;> simp [hy]
    rw [this]; exact (Reaches.refl _ _).of_step (step_dec_zero h0 hy)
  | succ n ih =>
    let σ' : ℕ → ℕ := fun i => if i = y then n else if i = d then σ d + 1 else σ i
    have hJ' : σ' J = 0 := by simp [σ', hJy, hJd, hJ]
    have hy' : σ' y = n := by simp [σ']
    have e1 := step_dec_pos h0 (σ := σ) (by omega)
    have e2 := step_inc h1 (σ := Function.update σ y (σ y - 1))
    have e12 : Function.update (Function.update σ y (σ y - 1)) d
        (Function.update σ y (σ y - 1) d + 1) = σ' := by
      funext i; simp only [Function.update_apply, σ']
      by_cases h1 : i = d <;> by_cases h2 : i = y <;> simp [h1, h2, hyd, hyd.symm] at * <;> (try omega)
    rw [e12] at e2
    have e3 := step_jmp h2 (σ := σ') hJ'
    refine Reaches.of_step e1 (Reaches.of_step e2 (Reaches.of_step e3 ?_))
    have := ih σ' hJ' hy'
    convert this using 3 with i
    simp only [σ']
    by_cases h1 : i = y <;> by_cases h2 : i = d <;> simp [h1, h2, hyd, hyd.symm] at * <;> (try omega)

/-- `transfer y d e`: move `y` into `d` and `e`. -/
theorem reaches_transfer2 {μ : Machine} {s J y d e : ℕ} (h0 : μ s = .dec y (s + 1) (s + 4))
    (h1 : μ (s + 1) = .inc d (s + 2)) (h2 : μ (s + 2) = .inc e (s + 3))
    (h3 : μ (s + 3) = jmp J s) (hyd : y ≠ d) (hye : y ≠ e) (hde : d ≠ e) (hJy : J ≠ y)
    (hJd : J ≠ d) (hJe : J ≠ e) (σ : ℕ → ℕ) (hJ : σ J = 0) :
    Reaches μ ⟨s, σ⟩ ⟨s + 4, fun i => if i = y then 0 else if i = d then σ d + σ y else
      if i = e then σ e + σ y else σ i⟩ := by
  induction hy : σ y generalizing σ with
  | zero =>
    have : (fun i => if i = y then 0 else if i = d then σ d + 0 else
        if i = e then σ e + 0 else σ i) = σ := by
      funext i; split_ifs with h1 h2 <;> subst_vars <;> simp [hy]
    rw [this]; exact (Reaches.refl _ _).of_step (step_dec_zero h0 hy)
  | succ n ih =>
    let σ' : ℕ → ℕ := fun i => if i = y then n else if i = d then σ d + 1 else
      if i = e then σ e + 1 else σ i
    have hJ' : σ' J = 0 := by simp [σ', hJy, hJd, hJe, hJ]
    have hy' : σ' y = n := by simp [σ']
    have e1 := step_dec_pos h0 (σ := σ) (by omega)
    have e2 := step_inc h1 (σ := Function.update σ y (σ y - 1))
    have e3 := step_inc h2 (σ := Function.update (Function.update σ y (σ y - 1)) d
      (Function.update σ y (σ y - 1) d + 1))
    have e123 : Function.update (Function.update (Function.update σ y (σ y - 1)) d
        (Function.update σ y (σ y - 1) d + 1)) e (Function.update (Function.update σ y
        (σ y - 1)) d (Function.update σ y (σ y - 1) d + 1) e + 1) = σ' := by
      funext i; simp only [Function.update_apply, σ']
      by_cases h1 : i = d <;> by_cases h2 : i = y <;> by_cases h3 : i = e <;>
        simp [h1, h2, h3, hyd, hyd.symm, hye, hye.symm, hde, hde.symm] at * <;> (try omega)
    rw [e123] at e3
    refine Reaches.of_step e1 (Reaches.of_step e2 (Reaches.of_step e3 (Reaches.of_step
      (step_jmp h3 hJ') ?_)))
    have := ih σ' hJ' hy'
    convert this using 3 with i
    simp only [σ']
    by_cases h1 : i = y <;> by_cases h2 : i = d <;> by_cases h3 : i = e <;>
      simp [h1, h2, h3, hyd, hyd.symm, hye, hye.symm, hde, hde.symm] at * <;> (try omega)

end ZInQ.Compiler.IR
