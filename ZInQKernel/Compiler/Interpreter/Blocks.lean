import ZInQKernel.Compiler.Interpreter.Program

/-!
# Arithmetic blocks of the interpreter

The semantics of the arithmetic blocks: `clear`, the preserving zero test `ifNZ`, `copyBlock`,
`addBlock`, the aliased addition `doubleBlock`, the comparison `ifLt`, `divModBlock` and
`divmod2`. Each completes normally from any register file with the jump register zero, with
the stated effect on its result registers; every register outside the block's registers is
unchanged. Scratch registers are cleared by the blocks before use, so they may hold anything
on entry, and they are not cleared on exit. By `compile_correct`, each statement becomes a run
of the compiled block (`Runs.reaches`).

(Blueprint: `compiler/natural/universal/interpreter-primitives.md`.)
-/

namespace ZInQ.Compiler.Universal

open RM Stmt

/-- `s` completes normally from `ρ` with the file `ρ'`. -/
def Runs (s : Stmt) (ρ ρ' : Regs) : Prop := Exec s ρ (.normal ρ')

/-- `ρ'` agrees with `ρ` outside the registers satisfying `S`. -/
def Frame (S : ℕ → Prop) (ρ ρ' : Regs) : Prop := ∀ k, ¬ S k → ρ' k = ρ k

theorem Frame.refl (S : ℕ → Prop) (ρ : Regs) : Frame S ρ ρ := fun _ _ => rfl

theorem Frame.trans {S : ℕ → Prop} {ρ₁ ρ₂ ρ₃ : Regs} (h₁ : Frame S ρ₁ ρ₂) (h₂ : Frame S ρ₂ ρ₃) :
    Frame S ρ₁ ρ₃ := fun k hk => (h₂ k hk).trans (h₁ k hk)

theorem Frame.mono {S T : ℕ → Prop} {ρ ρ' : Regs} (h : Frame S ρ ρ') (hST : ∀ k, S k → T k) :
    Frame T ρ ρ' := fun k hk => h k (fun hs => hk (hST k hs))

theorem Frame.update {S : ℕ → Prop} {ρ ρ' : Regs} (h : Frame S ρ ρ') {x : ℕ} (hx : S x)
    (v : ℕ) : Frame S ρ (Function.update ρ' x v) := fun k hk => by
  rw [Function.update_of_ne (fun e : k = x => hk (e ▸ hx))]
  exact h k hk

/-- The compiled code of a normally completing statement runs from its first state to the
state after it. -/
theorem Runs.reaches {s : Stmt} {ρ ρ' : Regs} (h : Runs s ρ ρ') {μ : Machine} {L ls le ex : ℕ}
    (hcode : CodeAt μ L (s.compile L ls le ex)) (hJ : ρ J = 0) :
    Reaches μ ⟨L, ρ⟩ ⟨L + s.size, ρ'⟩ :=
  compile_correct h hcode hJ

theorem Runs.of_eq {s : Stmt} {ρ ρ₁ ρ₂ : Regs} (h : Runs s ρ ρ₁) (e : ρ₁ = ρ₂) : Runs s ρ ρ₂ :=
  e ▸ h

theorem Runs.regs_J {s : Stmt} {ρ ρ' : Regs} (h : Runs s ρ ρ') (hJ : ρ J = 0) : ρ' J = 0 :=
  Exec.regs_J h hJ

theorem Runs.seq {s t : Stmt} {ρ ρ₁ ρ₂ : Regs} (h₁ : Runs s ρ ρ₁) (h₂ : Runs t ρ₁ ρ₂) :
    Runs (.seq s t) ρ ρ₂ := Exec.seq_normal h₁ h₂

theorem runs_seqs_nil (ρ : Regs) : Runs (seqs []) ρ ρ := Exec.skip ρ

theorem Runs.seqs_cons {s : Stmt} {ss : List Stmt} {ρ ρ₁ ρ₂ : Regs} (h₁ : Runs s ρ ρ₁)
    (h₂ : Runs (seqs ss) ρ₁ ρ₂) : Runs (seqs (s :: ss)) ρ ρ₂ := Exec.seq_normal h₁ h₂

theorem Runs.seqs_one {s : Stmt} {ρ ρ₁ : Regs} (h₁ : Runs s ρ ρ₁) : Runs (seqs [s]) ρ ρ₁ :=
  h₁.seqs_cons (runs_seqs_nil ρ₁)

theorem Exec.seqs_cons {s : Stmt} {ss : List Stmt} {ρ ρ₁ : Regs} {o : Outcome}
    (h₁ : Runs s ρ ρ₁) (h₂ : Exec (seqs ss) ρ₁ o) : Exec (seqs (s :: ss)) ρ o :=
  Exec.seq_normal h₁ h₂

theorem Exec.seqs_one' {s : Stmt} {ρ : Regs} {o : Outcome} (h : Exec s ρ o) (ho : o.IsAbnormal) :
    Exec (seqs [s]) ρ o := Exec.seq_abnormal h ho

theorem Exec.seqs_abnormal {s : Stmt} {ss : List Stmt} {ρ : Regs} {o : Outcome}
    (h₁ : Exec s ρ o) (ho : o.IsAbnormal) : Exec (seqs (s :: ss)) ρ o :=
  Exec.seq_abnormal h₁ ho

/-- Register-file extensionality, deciding every `Function.update` by cases. -/
macro "regs_ext" : tactic =>
  `(tactic| (funext k; simp only [Function.update_apply]; split_ifs <;> simp_all <;> omega))

/-! ### Primitive statements -/

theorem runs_clear (x : ℕ) (ρ : Regs) : Runs (clear x) ρ (Function.update ρ x 0) :=
  Exec.clear x ρ

theorem runs_inc {x : ℕ} (hx : x ≠ J) (ρ : Regs) :
    Runs (inc x) ρ (Function.update ρ x (ρ x + 1)) := Exec.inc x ρ hx

theorem runs_pred (x : ℕ) (ρ : Regs) : Runs (pred x) ρ (Function.update ρ x (ρ x - 1)) :=
  Exec.pred x ρ

/-- A `whileDec` loop whose body runs, from every file, to a file determined by a step
function; induction on the counter. -/
theorem runs_whileDec {x : ℕ} {b : Stmt} (f : Regs → Regs)
    (hb : ∀ σ, σ x ≠ 0 → Runs b (Function.update σ x (σ x - 1)) (f σ))
    (hfx : ∀ σ, σ x ≠ 0 → f σ x = σ x - 1) :
    ∀ n (σ : Regs), σ x = n → Runs (whileDec x b) σ (Nat.iterate f n σ) := by
  intro n
  induction n with
  | zero => intro σ hσ; exact Exec.while_zero hσ
  | succ n ih =>
    intro σ hσ
    refine Exec.while_normal (by omega) (hb σ (by omega)) ?_
    rw [Function.iterate_succ_apply]
    exact ih _ (by rw [hfx σ (by omega)]; omega)

/-! ### Copies and additions -/

/-- The moving loop `while y { x++; t++ }`. -/
theorem runs_move2 {x y t : ℕ} (hxy : x ≠ y) (hty : t ≠ y) (hxt : x ≠ t) (hx : x ≠ J)
    (ht : t ≠ J) : ∀ ρ : Regs,
    Runs (whileDec y (seqs [inc x, inc t])) ρ
      (Function.update (Function.update (Function.update ρ y 0) x (ρ x + ρ y)) t (ρ t + ρ y)) := by
  suffices ∀ n (ρ : Regs), ρ y = n → Runs (whileDec y (seqs [inc x, inc t])) ρ
      (Function.update (Function.update (Function.update ρ y 0) x (ρ x + ρ y)) t (ρ t + ρ y)) from
    fun ρ => this _ ρ rfl
  intro n
  induction n with
  | zero =>
    intro ρ hρ
    refine Runs.of_eq (Exec.while_zero (b := seqs [inc x, inc t]) hρ) ?_
    regs_ext
  | succ n ih =>
    intro ρ hρ
    set ρ₁ := Function.update ρ y (ρ y - 1)
    set ρ₂ := Function.update ρ₁ x (ρ₁ x + 1)
    set ρ₃ := Function.update ρ₂ t (ρ₂ t + 1)
    have hb : Runs (seqs [inc x, inc t]) ρ₁ ρ₃ :=
      (runs_inc hx ρ₁).seqs_cons ((runs_inc ht ρ₂).seqs_one)
    refine Exec.while_normal (by omega) hb ?_
    have h3 : ρ₃ y = n := by simp [ρ₃, ρ₂, ρ₁, Function.update_apply, hxy.symm, hty.symm]; omega
    refine (ih ρ₃ h3).of_eq ?_
    simp only [ρ₃, ρ₂, ρ₁]
    regs_ext

/-- The restoring loop `while t { y++ }`. -/
theorem runs_move1 {t y : ℕ} (hty : t ≠ y) : ∀ ρ : Regs, (y ≠ J ∨ ρ t = 0) →
    Runs (whileDec t (inc y)) ρ (Function.update (Function.update ρ t 0) y (ρ y + ρ t)) := by
  suffices ∀ n (ρ : Regs), ρ t = n → (y ≠ J ∨ ρ t = 0) →
      Runs (whileDec t (inc y)) ρ (Function.update (Function.update ρ t 0) y (ρ y + ρ t)) from
    fun ρ => this _ ρ rfl
  intro n
  induction n with
  | zero =>
    intro ρ hρ _
    refine Runs.of_eq (Exec.while_zero (b := inc y) hρ) ?_
    regs_ext
  | succ n ih =>
    intro ρ hρ hy
    have hy : y ≠ J := by omega
    set ρ₁ := Function.update ρ t (ρ t - 1)
    set ρ₂ := Function.update ρ₁ y (ρ₁ y + 1)
    refine Exec.while_normal (by omega) (runs_inc hy ρ₁) ?_
    have h2 : ρ₂ t = n := by simp [ρ₂, ρ₁, Function.update_apply, hty]; omega
    refine (ih ρ₂ h2 (Or.inl hy)).of_eq ?_
    simp only [ρ₂, ρ₁]
    regs_ext

/-- **Copy** `x ← y` through the scratch counter `t`; `y` is restored. The source may be the
jump register (which is zero). -/
theorem runs_copyBlock {x y t : ℕ} (hxy : x ≠ y) (hxt : x ≠ t) (hyt : y ≠ t) (hx : x ≠ J)
    (ht : t ≠ J) (ρ : Regs) (hJ : ρ J = 0) :
    Runs (copyBlock x y t) ρ (Function.update (Function.update ρ x (ρ y)) t 0) := by
  set ρ₁ := Function.update ρ x 0
  set ρ₂ := Function.update ρ₁ t 0
  have h1 := runs_clear x ρ
  have h2 := runs_clear t ρ₁
  have h3 := runs_move2 hxy hyt.symm hxt hx ht ρ₂
  set ρ₃ := Function.update (Function.update (Function.update ρ₂ y 0) x (ρ₂ x + ρ₂ y)) t
    (ρ₂ t + ρ₂ y)
  have h4 := runs_move1 hyt.symm ρ₃ (by
    by_cases hyJ : y = J
    · right; simp [ρ₃, ρ₂, ρ₁, Function.update_apply, hyJ, hJ]
    · left; exact hyJ)
  refine (h1.seqs_cons (h2.seqs_cons (h3.seqs_cons h4.seqs_one))).of_eq ?_
  simp only [ρ₃, ρ₂, ρ₁]
  regs_ext

/-- **Addition** `x ← x + y` through the scratch counter `t`, for `x ≠ y`; `y` is restored. -/
theorem runs_addBlock {x y t : ℕ} (hxy : x ≠ y) (hxt : x ≠ t) (hyt : y ≠ t) (hx : x ≠ J)
    (ht : t ≠ J) (hy : y ≠ J) (ρ : Regs) :
    Runs (addBlock x y t) ρ (Function.update (Function.update ρ x (ρ x + ρ y)) t 0) := by
  set ρ₁ := Function.update ρ t 0
  have h1 := runs_clear t ρ
  have h2 := runs_move2 hxy hyt.symm hxt hx ht ρ₁
  set ρ₂ := Function.update (Function.update (Function.update ρ₁ y 0) x (ρ₁ x + ρ₁ y)) t
    (ρ₁ t + ρ₁ y)
  have h3 := runs_move1 hyt.symm ρ₂ (Or.inl hy)
  refine (h1.seqs_cons (h2.seqs_cons h3.seqs_one)).of_eq ?_
  simp only [ρ₂, ρ₁]
  regs_ext

/-- **Aliased addition** `x ← x + x`: the operand is snapshot into `s` before `x` is
overwritten. -/
theorem runs_doubleBlock {x s t₁ t₂ : ℕ} (hxs : x ≠ s) (hxt₁ : x ≠ t₁) (hxt₂ : x ≠ t₂)
    (hst₁ : s ≠ t₁) (hst₂ : s ≠ t₂) (hx : x ≠ J) (hs : s ≠ J) (ht₁ : t₁ ≠ J)
    (ht₂ : t₂ ≠ J) (ρ : Regs) (hJ : ρ J = 0) :
    Runs (doubleBlock x s t₁ t₂) ρ
      (Function.update (Function.update (Function.update (Function.update ρ s (ρ x)) t₁ 0) x
        (ρ x + ρ x)) t₂ 0) := by
  have h1 := runs_copyBlock hxs.symm hst₁ hxt₁ hs ht₁ ρ hJ
  set ρ₁ := Function.update (Function.update ρ s (ρ x)) t₁ 0
  have h2 := runs_addBlock hxs hxt₂ hst₂ hx ht₂ hs ρ₁
  refine (h1.seqs_cons h2.seqs_one).of_eq ?_
  simp only [ρ₁]
  regs_ext

/-- The subtraction loop `while c { x-- }`. -/
theorem runs_subLoop {c x : ℕ} (hcx : c ≠ x) : ∀ ρ : Regs,
    Runs (whileDec c (pred x)) ρ (Function.update (Function.update ρ c 0) x (ρ x - ρ c)) := by
  suffices ∀ n (ρ : Regs), ρ c = n →
      Runs (whileDec c (pred x)) ρ (Function.update (Function.update ρ c 0) x (ρ x - ρ c)) from
    fun ρ => this _ ρ rfl
  intro n
  induction n with
  | zero =>
    intro ρ hρ
    refine Runs.of_eq (Exec.while_zero (b := pred x) hρ) ?_
    regs_ext
  | succ n ih =>
    intro ρ hρ
    set ρ₁ := Function.update ρ c (ρ c - 1)
    set ρ₂ := Function.update ρ₁ x (ρ₁ x - 1)
    refine Exec.while_normal (by omega) (runs_pred x ρ₁) ?_
    have h2 : ρ₂ c = n := by simp [ρ₂, ρ₁, Function.update_apply, hcx]; omega
    refine (ih ρ₂ h2).of_eq ?_
    simp only [ρ₂, ρ₁]
    regs_ext

/-- `omega`, knowing that the jump register is `2`. -/
macro "omegaJ" : tactic => `(tactic| (have : J = 2 := rfl; omega))

/-- Evaluate `Function.update` chains at registers whose disequalities follow by `omega`. -/
macro "upd" : tactic =>
  `(tactic| simp (disch := omegaJ) only [Function.update_self, Function.update_of_ne])

/-- The scratch registers `b, …, b + n - 1`. -/
def Scratch (b n k : ℕ) : Prop := b ≤ k ∧ k < b + n

theorem Frame.upd {S : ℕ → Prop} {ρ ρ' : Regs} {x : ℕ} (hx : S x) (v : ℕ)
    (h : Frame S ρ ρ') : Frame S ρ (Function.update ρ' x v) := h.update hx v

/-- Close a frame goal through a chain of updates of scratch registers. -/
macro "frame_scratch" : tactic =>
  `(tactic| ((repeat (refine Frame.upd ⟨by omegaJ, by omegaJ⟩ _ ?_)) <;>
    first | assumption | exact Frame.refl _ _))

/-- The remainder loop of `divModBlock`: from a file with `y = q z + r` in the registers
`b + 1`, `b`, it reaches a file with the same invariant and `r < z`. -/
theorem runs_divModLoop {y z b : ℕ} (hzb : z < b ∨ b + 11 ≤ z)
    (hJb : J < b) (ρ : Regs) (hJ : ρ J = 0) (hz : 0 < ρ z) :
    ∀ σ : Regs, Frame (Scratch b 11) ρ σ → σ (b + 1) * ρ z + σ b = ρ y →
      ∃ σ', Runs (loop (seqs [copyBlock (b + 4) b (b + 6), copyBlock (b + 5) z (b + 7),
        ifLt (b + 4) (b + 5) (seqs [brk])
          (seqs [copyBlock (b + 2) z (b + 8), whileDec (b + 2) (pred b), inc (b + 1), cont])]))
        σ σ' ∧ Frame (Scratch b 11) ρ σ' ∧ σ' (b + 1) * ρ z + σ' b = ρ y ∧ σ' b < ρ z := by
  suffices ∀ n σ, σ b = n → Frame (Scratch b 11) ρ σ → σ (b + 1) * ρ z + σ b = ρ y →
      ∃ σ', Runs (loop (seqs [copyBlock (b + 4) b (b + 6), copyBlock (b + 5) z (b + 7),
        ifLt (b + 4) (b + 5) (seqs [brk])
          (seqs [copyBlock (b + 2) z (b + 8), whileDec (b + 2) (pred b), inc (b + 1), cont])]))
        σ σ' ∧ Frame (Scratch b 11) ρ σ' ∧ σ' (b + 1) * ρ z + σ' b = ρ y ∧ σ' b < ρ z from
    fun σ => this _ σ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hn hσ hinv
    have hσJ : σ J = 0 := by rw [hσ J (by unfold Scratch; omega), hJ]
    have hσz : σ z = ρ z := hσ z (by unfold Scratch; omega)
    have h1 := runs_copyBlock (x := b + 4) (y := b) (t := b + 6) (by omega) (by omega) (by omega)
      (by omega) (by omega) σ hσJ
    set σ₁ := Function.update (Function.update σ (b + 4) (σ b)) (b + 6) 0 with hσ₁
    have hσ₁J : σ₁ J = 0 := by rw [hσ₁]; upd; exact hσJ
    have h2 := runs_copyBlock (x := b + 5) (y := z) (t := b + 7) (by omega) (by omega) (by omega)
      (by omega) (by omega) σ₁ hσ₁J
    set σ₂ := Function.update (Function.update σ₁ (b + 5) (σ₁ z)) (b + 7) 0 with hσ₂
    have ha : σ₂ (b + 4) = σ b := by rw [hσ₂, hσ₁]; upd
    have hb' : σ₂ (b + 5) = ρ z := by rw [hσ₂, hσ₁]; upd; exact hσz
    have hfr₂ : Frame (Scratch b 11) ρ σ₂ := by rw [hσ₂, hσ₁]; frame_scratch
    by_cases hlt : σ b < ρ z
    · -- the remainder is below the divisor: break
      set σ₃ := Function.update (Function.update σ₂ (b + 4) 0) (b + 5)
        (σ₂ (b + 5) - σ₂ (b + 4) - 1) with hσ₃
      have hif : Exec (ifLt (b + 4) (b + 5) (seqs [brk])
          (seqs [copyBlock (b + 2) z (b + 8), whileDec (b + 2) (pred b), inc (b + 1), cont]))
          σ₂ (.brk σ₃) :=
        Exec.ifLt_lt (by omega) (by rw [ha, hb']; exact hlt)
          (Exec.seqs_abnormal (Exec.brk _) trivial)
      refine ⟨σ₃, Exec.loop_brk (Exec.seqs_cons h1 (Exec.seqs_cons h2
        (Exec.seqs_abnormal hif trivial))),
        ?_, ?_, ?_⟩
      · rw [hσ₃]; frame_scratch
      · have e1 : σ₃ (b + 1) = σ (b + 1) := by rw [hσ₃, hσ₂, hσ₁]; upd
        have e2 : σ₃ b = σ b := by rw [hσ₃, hσ₂, hσ₁]; upd
        rw [e1, e2]; exact hinv
      · have e2 : σ₃ b = σ b := by rw [hσ₃, hσ₂, hσ₁]; upd
        rw [e2]; exact hlt
    · -- subtract the divisor and continue
      rw [not_lt] at hlt
      set σ₃ := Function.update (Function.update σ₂ (b + 4) (σ₂ (b + 4) - σ₂ (b + 5))) (b + 5) 0
        with hσ₃
      have hσ₃J : σ₃ J = 0 := by rw [hσ₃, hσ₂, hσ₁]; upd; exact hσJ
      have h4 := runs_copyBlock (x := b + 2) (y := z) (t := b + 8) (by omega) (by omega)
        (by omega) (by omega) (by omega) σ₃ hσ₃J
      set σ₄ := Function.update (Function.update σ₃ (b + 2) (σ₃ z)) (b + 8) 0 with hσ₄
      have h5 := runs_subLoop (c := b + 2) (x := b) (by omega) σ₄
      set σ₅ := Function.update (Function.update σ₄ (b + 2) 0) b (σ₄ b - σ₄ (b + 2)) with hσ₅
      have h6 := runs_inc (x := b + 1) (by omega) σ₅
      set σ₆ := Function.update σ₅ (b + 1) (σ₅ (b + 1) + 1) with hσ₆
      have hz4 : σ₄ (b + 2) = ρ z := by rw [hσ₄, hσ₃, hσ₂, hσ₁]; upd; exact hσz
      have hb4 : σ₄ b = σ b := by rw [hσ₄, hσ₃, hσ₂, hσ₁]; upd
      have e6b : σ₆ b = σ b - ρ z := by rw [hσ₆, hσ₅]; upd; rw [hb4, hz4]
      have e6q : σ₆ (b + 1) = σ (b + 1) + 1 := by
        rw [hσ₆, hσ₅, hσ₄, hσ₃, hσ₂, hσ₁]; upd
      have hfr₆ : Frame (Scratch b 11) ρ σ₆ := by
        rw [hσ₆, hσ₅, hσ₄, hσ₃]; frame_scratch
      have hif : Exec (ifLt (b + 4) (b + 5) (seqs [brk])
          (seqs [copyBlock (b + 2) z (b + 8), whileDec (b + 2) (pred b), inc (b + 1), cont]))
          σ₂ (.cont σ₆) :=
        Exec.ifLt_ge (by omega) (by rw [ha, hb']; exact hlt)
          (Exec.seqs_cons h4 (Exec.seqs_cons h5 (Exec.seqs_cons h6
            (Exec.seqs_abnormal (Exec.cont _) trivial))))
      obtain ⟨σ', hrun, hfr, hinv', hlt'⟩ := ih (σ₆ b) (by rw [e6b]; omega) σ₆ rfl hfr₆ (by
        rw [e6b, e6q, add_mul, one_mul]
        omega)
      exact ⟨σ', Exec.loop_cont (Exec.seqs_cons h1 (Exec.seqs_cons h2
          (Exec.seqs_abnormal hif trivial)))
        hrun,
        hfr, hinv', hlt'⟩

/-- **Division** `q ← ⌊y / z⌋`, `r ← y mod z` for `z ≥ 1`, with scratch registers
`b, …, b + 10`; every other register is unchanged. -/
theorem runs_divModBlock {y z q r b : ℕ} (hyb : y < b ∨ b + 11 ≤ y) (hzb : z < b ∨ b + 11 ≤ z)
    (hqb : q < b ∨ b + 11 ≤ q) (hrb : r < b ∨ b + 11 ≤ r) (hJb : J < b) (hqr : q ≠ r)
    (hqJ : q ≠ J) (hrJ : r ≠ J) (hqy : q ≠ y) (hqz : q ≠ z) (hry : r ≠ y) (hrz : r ≠ z)
    (ρ : Regs) (hJ : ρ J = 0) (hz : 0 < ρ z) :
    ∃ ρ', Runs (divModBlock y z q r b) ρ ρ' ∧ ρ' q = ρ y / ρ z ∧ ρ' r = ρ y % ρ z ∧
      Frame (fun k => k = q ∨ k = r ∨ Scratch b 11 k) ρ ρ' := by
  have h1 := runs_copyBlock (x := b) (y := y) (t := b + 3) (by omega) (by omega) (by omega)
    (by omega) (by omega) ρ hJ
  set ρ₁ := Function.update (Function.update ρ b (ρ y)) (b + 3) 0 with hρ₁
  have h2 := runs_clear (b + 1) ρ₁
  set ρ₂ := Function.update ρ₁ (b + 1) 0 with hρ₂
  have hfr₂ : Frame (Scratch b 11) ρ ρ₂ := by
    rw [hρ₂, hρ₁]; frame_scratch
  obtain ⟨σ, hrun, hfr, hinv, hlt⟩ := runs_divModLoop (y := y) hzb hJb ρ hJ hz ρ₂ hfr₂ (by
    rw [hρ₂, hρ₁]; upd; simp)
  have hσJ : σ J = 0 := by rw [hfr J (by unfold Scratch; omega), hJ]
  have h3 := runs_copyBlock (x := q) (y := b + 1) (t := b + 9) (by omega) (by omega) (by omega)
    (by omega) (by omega) σ hσJ
  set ρ₃ := Function.update (Function.update σ q (σ (b + 1))) (b + 9) 0 with hρ₃
  have hρ₃J : ρ₃ J = 0 := by rw [hρ₃]; upd; exact hσJ
  have h4 := runs_copyBlock (x := r) (y := b) (t := b + 10) (by omega) (by omega) (by omega)
    (by omega) (by omega) ρ₃ hρ₃J
  set ρ₄ := Function.update (Function.update ρ₃ r (ρ₃ b)) (b + 10) 0 with hρ₄
  have hdm := (Nat.div_mod_unique (a := ρ y) (d := σ (b + 1)) (c := σ b) hz).2
    ⟨by rw [mul_comm]; omega, hlt⟩
  refine ⟨ρ₄, h1.seqs_cons (h2.seqs_cons (hrun.seqs_cons (h3.seqs_cons h4.seqs_one))),
    ?_, ?_, ?_⟩
  · rw [hρ₄, hρ₃]; upd; exact hdm.1.symm
  · rw [hρ₄, hρ₃]; upd; exact hdm.2.symm
  · intro k hk
    simp only [not_or, Scratch] at hk
    rw [hρ₄, hρ₃]; upd
    exact hfr k (by unfold Scratch; omega)

end ZInQ.Compiler.Universal
