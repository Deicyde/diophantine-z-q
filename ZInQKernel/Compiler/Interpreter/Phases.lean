import ZInQKernel.Compiler.Interpreter.ListBlocks

/-!
# The phases of one interpreter loop

The loop body of the interpreter is `fetch; opcode; get; exec; set; cont`. With `D`, `β`, `pc`
and the tape in registers `4`, `5`, `6`, `7`:

* `fetchStmt` reads the base-`β` digits `o, j, x, y` of `D` at positions `4 pc, …, 4 pc + 3`
  into registers `11, …, 14`, by `4 pc` divisions by `β` and four division-with-remainder steps;
* `opcodeStmt` exits to cleanup unless `o ∈ {1, 2}`;
* `getStmt` reads `v = get(tape, j)` into register `8`;
* `execStmt` replaces `v` by `v + 1` (`o = 1`) or `v - 1` (`o = 2`, `v > 0`) and sets `pc` to
  `x`, or to `y` when `o = 2` and `v = 0`;
* `setStmt` stores `set(tape, j, v)` in register `7`.

Every phase leaves the registers outside its `writes` list unchanged
(`Exec.regs_of_not_mem_writes`).

(Blueprint: `compiler/natural/universal/interpreter-step.md`.)
-/

namespace ZInQ.Compiler.Universal

open RM Stmt

theorem Runs.frame {s : Stmt} {ρ ρ' : Regs} (h : Runs s ρ ρ') (k : ℕ) (hk : k ∉ s.writes) :
    ρ' k = ρ k := Exec.regs_of_not_mem_writes h k hk

theorem Runs.seqs_append {l₂ : List Stmt} : ∀ {l₁ : List Stmt} {ρ ρ₁ ρ₂ : Regs},
    Runs (seqs l₁) ρ ρ₁ → Runs (seqs l₂) ρ₁ ρ₂ → Runs (seqs (l₁ ++ l₂)) ρ ρ₂
  | [], _, _, _, h₁, h₂ => by cases h₁; exact h₂
  | _ :: _, _, _, _, h₁, h₂ => by
    cases h₁ with
    | seq_normal ha hl => exact Exec.seq_normal ha (Runs.seqs_append hl h₂)
    | seq_abnormal _ hab => exact hab.elim

/-! ### Fetch -/

/-- The shift loop: `4 pc` divisions of register `9` by `β`. -/
theorem runs_shiftLoop : ∀ n (σ : Regs), σ 10 = n → σ J = 0 → 0 < σ 5 →
    ∃ σ', Runs (whileDec 10 (seqs [divModBlock 9 5 15 16 48, copyBlock 9 15 59])) σ σ' ∧
      σ' 9 = σ 9 / σ 5 ^ n ∧
      Frame (fun k => k = 9 ∨ k = 10 ∨ k = 15 ∨ k = 16 ∨ Scratch 48 12 k) σ σ' := by
  intro n
  induction n with
  | zero => intro σ hσ _ _; exact ⟨σ, Exec.while_zero hσ, by simp, Frame.refl _ _⟩
  | succ n ih =>
    intro σ hσ hJ hβ
    set σ₁ := Function.update σ 10 (σ 10 - 1) with hσ₁
    have hσ₁J : σ₁ J = 0 := by rw [hσ₁]; upd; exact hJ
    obtain ⟨σ₂, h2, e2q, -, hfr₂⟩ := runs_divModBlock (y := 9) (z := 5) (q := 15) (r := 16)
      (b := 48) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ)
      (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) σ₁ hσ₁J
      (by rw [hσ₁]; upd; exact hβ)
    have hσ₂J : σ₂ J = 0 := by rw [hfr₂ J (by unfold Scratch; omegaJ), hσ₁J]
    have h3 := runs_copyBlock (x := 9) (y := 15) (t := 59) (by omegaJ) (by omegaJ) (by omegaJ)
      (by omegaJ) (by omegaJ) σ₂ hσ₂J
    set σ₃ := Function.update (Function.update σ₂ 9 (σ₂ 15)) 59 0 with hσ₃
    have e3_5 : σ₃ 5 = σ 5 := by
      rw [hσ₃]; upd; rw [hfr₂ 5 (by unfold Scratch; omegaJ), hσ₁]; upd
    have e3_10 : σ₃ 10 = n := by
      rw [hσ₃]; upd; rw [hfr₂ 10 (by unfold Scratch; omegaJ), hσ₁]; upd; omega
    have e3_9 : σ₃ 9 = σ 9 / σ 5 := by
      rw [hσ₃]; upd; rw [e2q, hσ₁]; upd
    have hσ₃J : σ₃ J = 0 := by rw [hσ₃]; upd; exact hσ₂J
    obtain ⟨σ', h', e', hfr'⟩ := ih σ₃ e3_10 hσ₃J (by rw [e3_5]; exact hβ)
    refine ⟨σ', Exec.while_normal (by omegaJ) (h2.seqs_cons h3.seqs_one) h', ?_, ?_⟩
    · rw [e', e3_9, e3_5, Nat.div_div_eq_div_mul, pow_succ']
    · intro k hk
      simp only [Scratch, not_or] at hk
      rw [hfr' k (by simp only [Scratch, not_or]; omegaJ), hσ₃]; upd
      rw [hfr₂ k (by unfold Scratch; omegaJ), hσ₁]; upd

/-- One digit: `d ← r9 mod β`, `r9 ← r9 / β`. -/
theorem runs_digit {d b t : ℕ} (hdb : d < b) (hdJ : d ≠ J) (hd : d ≠ 9) (hd5 : d ≠ 5)
    (hd15 : d ≠ 15) (hb : 15 < b) (ht : t = b + 11) (σ : Regs) (hJ : σ J = 0) (hβ : 0 < σ 5) :
    ∃ σ', Runs (seqs [divModBlock 9 5 15 d b, copyBlock 9 15 t]) σ σ' ∧
      σ' d = σ 9 % σ 5 ∧ σ' 9 = σ 9 / σ 5 ∧
      Frame (fun k => k = 9 ∨ k = 15 ∨ k = d ∨ Scratch b 12 k) σ σ' := by
  obtain ⟨σ₂, h2, e2q, e2r, hfr₂⟩ := runs_divModBlock (y := 9) (z := 5) (q := 15) (r := d)
    (b := b) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ)
    hdJ (by omegaJ) (by omegaJ) hd hd5 σ hJ hβ
  have hσ₂J : σ₂ J = 0 := by rw [hfr₂ J (by unfold Scratch; omegaJ), hJ]
  have h3 := runs_copyBlock (x := 9) (y := 15) (t := t) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) σ₂ hσ₂J
  refine ⟨_, h2.seqs_cons h3.seqs_one, ?_, ?_, ?_⟩
  · upd; exact e2r
  · upd; exact e2q
  · intro k hk
    simp only [Scratch, not_or] at hk
    upd
    exact hfr₂ k (by unfold Scratch; omegaJ)

/-- **Fetch**: the four base-`β` digits of `D` at positions `4 pc, …, 4 pc + 3`. -/
theorem runs_fetchStmt (σ : Regs) (hJ : σ J = 0) (hβ : 0 < σ 5) :
    ∃ σ', Runs fetchStmt σ σ' ∧
      σ' 11 = σ 4 / σ 5 ^ (4 * σ 6) % σ 5 ∧ σ' 12 = σ 4 / σ 5 ^ (4 * σ 6 + 1) % σ 5 ∧
      σ' 13 = σ 4 / σ 5 ^ (4 * σ 6 + 2) % σ 5 ∧ σ' 14 = σ 4 / σ 5 ^ (4 * σ 6 + 3) % σ 5 ∧
      Frame (fun k => (9 ≤ k ∧ k ≤ 16) ∨ (43 ≤ k ∧ k ≤ 107)) σ σ' := by
  have h1 := runs_copyBlock (x := 9) (y := 4) (t := 43) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) σ hJ
  set τ₁ := Function.update (Function.update σ 9 (σ 4)) 43 0 with hτ₁
  have hτ₁J : τ₁ J = 0 := by rw [hτ₁]; upd; exact hJ
  have h2 := runs_copyBlock (x := 10) (y := 6) (t := 44) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) τ₁ hτ₁J
  set τ₂ := Function.update (Function.update τ₁ 10 (τ₁ 6)) 44 0 with hτ₂
  have h3 := runs_addBlock (x := 10) (y := 6) (t := 45) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) (by omegaJ) τ₂
  set τ₃ := Function.update (Function.update τ₂ 10 (τ₂ 10 + τ₂ 6)) 45 0 with hτ₃
  have h4 := runs_addBlock (x := 10) (y := 6) (t := 46) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) (by omegaJ) τ₃
  set τ₄ := Function.update (Function.update τ₃ 10 (τ₃ 10 + τ₃ 6)) 46 0 with hτ₄
  have h5 := runs_addBlock (x := 10) (y := 6) (t := 47) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) (by omegaJ) τ₄
  set τ₅ := Function.update (Function.update τ₄ 10 (τ₄ 10 + τ₄ 6)) 47 0 with hτ₅
  have e5_10 : τ₅ 10 = 4 * σ 6 := by rw [hτ₅, hτ₄, hτ₃, hτ₂, hτ₁]; upd; ring
  have e5_9 : τ₅ 9 = σ 4 := by rw [hτ₅, hτ₄, hτ₃, hτ₂, hτ₁]; upd
  have e5_5 : τ₅ 5 = σ 5 := by rw [hτ₅, hτ₄, hτ₃, hτ₂, hτ₁]; upd
  have hτ₅J : τ₅ J = 0 := by rw [hτ₅, hτ₄, hτ₃, hτ₂, hτ₁]; upd; exact hJ
  obtain ⟨τ₆, h6, e6_9, hfr₆⟩ := runs_shiftLoop _ τ₅ e5_10 hτ₅J (by rw [e5_5]; exact hβ)
  have e6_5 : τ₆ 5 = σ 5 := by rw [hfr₆ 5 (by unfold Scratch; omegaJ), e5_5]
  have hτ₆J : τ₆ J = 0 := h6.regs_J hτ₅J
  obtain ⟨τ₇, h7, e7d, e7_9, hfr₇⟩ := runs_digit (d := 11) (b := 60) (t := 71) (by omegaJ)
    (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) rfl τ₆ hτ₆J (by rw [e6_5]; exact hβ)
  have e7_5 : τ₇ 5 = σ 5 := by rw [hfr₇ 5 (by unfold Scratch; omegaJ), e6_5]
  have hτ₇J : τ₇ J = 0 := by rw [hfr₇ J (by unfold Scratch; omegaJ), hτ₆J]
  obtain ⟨τ₈, h8, e8d, e8_9, hfr₈⟩ := runs_digit (d := 12) (b := 72) (t := 83) (by omegaJ)
    (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) rfl τ₇ hτ₇J (by rw [e7_5]; exact hβ)
  have e8_5 : τ₈ 5 = σ 5 := by rw [hfr₈ 5 (by unfold Scratch; omegaJ), e7_5]
  have hτ₈J : τ₈ J = 0 := by rw [hfr₈ J (by unfold Scratch; omegaJ), hτ₇J]
  obtain ⟨τ₉, h9, e9d, e9_9, hfr₉⟩ := runs_digit (d := 13) (b := 84) (t := 95) (by omegaJ)
    (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) rfl τ₈ hτ₈J (by rw [e8_5]; exact hβ)
  have e9_5 : τ₉ 5 = σ 5 := by rw [hfr₉ 5 (by unfold Scratch; omegaJ), e8_5]
  have hτ₉J : τ₉ J = 0 := by rw [hfr₉ J (by unfold Scratch; omegaJ), hτ₈J]
  obtain ⟨τ₁₀, h10, e10d, -, hfr₁₀⟩ := runs_digit (d := 14) (b := 96) (t := 107) (by omegaJ)
    (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) rfl τ₉ hτ₉J (by rw [e9_5]; exact hβ)
  have hrun : Runs fetchStmt σ τ₁₀ := by
    unfold fetchStmt
    exact h1.seqs_cons (h2.seqs_cons (h3.seqs_cons (h4.seqs_cons (h5.seqs_cons (h6.seqs_cons
      (h7.seqs_append (h8.seqs_append (h9.seqs_append h10))))))))
  have hdig : ∀ k, τ₆ 9 / σ 5 ^ k = σ 4 / σ 5 ^ (4 * σ 6 + k) := by
    intro k; rw [e6_9, e5_9, e5_5, Nat.div_div_eq_div_mul, ← pow_add]
  refine ⟨τ₁₀, hrun, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr₁₀ 11 (by unfold Scratch; omegaJ), hfr₉ 11 (by unfold Scratch; omegaJ),
      hfr₈ 11 (by unfold Scratch; omegaJ), e7d, e6_5]
    have := hdig 0; simp only [pow_zero, Nat.div_one, add_zero] at this; rw [this]
  · rw [hfr₁₀ 12 (by unfold Scratch; omegaJ), hfr₉ 12 (by unfold Scratch; omegaJ), e8d, e7_9,
      e7_5, e6_5]
    have := hdig 1; simp only [pow_one] at this; rw [this]
  · rw [hfr₁₀ 13 (by unfold Scratch; omegaJ), e9d, e8_9, e8_5, e7_9, e7_5, e6_5,
      Nat.div_div_eq_div_mul, ← pow_two, hdig 2]
  · rw [e10d, e9_9, e9_5, e8_9, e8_5, e7_9, e7_5, e6_5, Nat.div_div_eq_div_mul,
      Nat.div_div_eq_div_mul, ← hdig 3]
    congr 2; ring
  · intro k hk
    simp only [not_or, not_and_or, not_le] at hk
    rw [hfr₁₀ k (by unfold Scratch; omegaJ), hfr₉ k (by unfold Scratch; omegaJ),
      hfr₈ k (by unfold Scratch; omegaJ), hfr₇ k (by unfold Scratch; omegaJ),
      hfr₆ k (by unfold Scratch; omegaJ), hτ₅, hτ₄, hτ₃, hτ₂, hτ₁]
    upd

/-! ### Opcode -/

/-- **Opcode test**, `o ∈ {1, 2}`: the phase completes normally. -/
theorem runs_opcodeStmt (σ : Regs) (hJ : σ J = 0) (ho : σ 11 = 1 ∨ σ 11 = 2) :
    ∃ σ', Runs opcodeStmt σ σ' ∧ Frame (fun k => k = 18 ∨ k = 108) σ σ' := by
  have h1 := runs_copyBlock (x := 18) (y := 11) (t := 108) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) σ hJ
  set τ₁ := Function.update (Function.update σ 18 (σ 11)) 108 0 with hτ₁
  have e1 : τ₁ 18 = σ 11 := by rw [hτ₁]; upd
  have h2 : Runs (ifNZ 18 (pred 18) exit) τ₁ (Function.update τ₁ 18 (τ₁ 18 - 1)) :=
    Exec.ifNZ_pos (by omega) (runs_pred 18 τ₁)
  set τ₂ := Function.update τ₁ 18 (τ₁ 18 - 1) with hτ₂
  rcases ho with ho | ho
  · have h3 : Runs (ifNZ 18 (seqs [pred 18, ifNZ 18 exit skip]) skip) τ₂ τ₂ :=
      Exec.ifNZ_zero (by rw [hτ₂]; upd; omega) (Exec.skip _)
    refine ⟨τ₂, h1.seqs_cons (h2.seqs_cons h3.seqs_one), ?_⟩
    rw [hτ₂, hτ₁]
    exact Frame.upd (Or.inl rfl) _ (Frame.upd (Or.inr rfl) _ (Frame.upd (Or.inl rfl) _
      (Frame.refl _ _)))
  · set τ₃ := Function.update τ₂ 18 (τ₂ 18 - 1) with hτ₃
    have h3 : Runs (ifNZ 18 (seqs [pred 18, ifNZ 18 exit skip]) skip) τ₂ τ₃ :=
      Exec.ifNZ_pos (by rw [hτ₂]; upd; omega) ((runs_pred 18 τ₂).seqs_cons
        (Runs.seqs_one (Exec.ifNZ_zero (by upd; rw [hτ₂]; upd; omega) (Exec.skip _))))
    refine ⟨τ₃, h1.seqs_cons (h2.seqs_cons h3.seqs_one), ?_⟩
    rw [hτ₃, hτ₂, hτ₁]
    exact Frame.upd (Or.inl rfl) _ (Frame.upd (Or.inl rfl) _ (Frame.upd (Or.inr rfl) _
      (Frame.upd (Or.inl rfl) _ (Frame.refl _ _))))

/-- **Opcode test**, `o ∉ {1, 2}`: the phase exits to cleanup. -/
theorem exec_opcodeStmt_exit (σ : Regs) (hJ : σ J = 0) (h1 : σ 11 ≠ 1) (h2 : σ 11 ≠ 2) :
    ∃ σ', Exec opcodeStmt σ (.exit σ') := by
  have r1 := runs_copyBlock (x := 18) (y := 11) (t := 108) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) σ hJ
  set τ₁ := Function.update (Function.update σ 18 (σ 11)) 108 0 with hτ₁
  have e1 : τ₁ 18 = σ 11 := by rw [hτ₁]; upd
  by_cases h0 : σ 11 = 0
  · exact ⟨τ₁, Exec.seqs_cons r1 (Exec.seqs_abnormal
      (Exec.ifNZ_zero (by rw [e1, h0]) (Exec.exit _)) trivial)⟩
  · have r2 : Runs (ifNZ 18 (pred 18) exit) τ₁ (Function.update τ₁ 18 (τ₁ 18 - 1)) :=
      Exec.ifNZ_pos (by omega) (runs_pred 18 τ₁)
    set τ₂ := Function.update τ₁ 18 (τ₁ 18 - 1) with hτ₂
    set τ₃ := Function.update τ₂ 18 (τ₂ 18 - 1) with hτ₃
    refine ⟨τ₃, Exec.seqs_cons r1 (Exec.seqs_cons r2 (Exec.seqs_abnormal ?_ trivial))⟩
    exact Exec.ifNZ_pos (by rw [hτ₂]; upd; omega) (Exec.seqs_cons (runs_pred 18 τ₂)
      (Exec.seqs_abnormal (Exec.ifNZ_pos (by upd; rw [hτ₂]; upd; omega) (Exec.exit _)) trivial))

/-! ### Get -/

/-- The walk of `getStmt`: `n` tail links. -/
theorem runs_getWalk : ∀ n (σ : Regs), σ 110 = n → σ J = 0 →
    ∃ σ', Runs (whileDec 110 (seqs [unconsBlock 109 111 112 115, copyBlock 109 112 123])) σ σ' ∧
      listGet (σ' 109) 0 = listGet (σ 109) n ∧ Frame (fun k => 109 ≤ k ∧ k ≤ 123) σ σ' := by
  intro n
  induction n with
  | zero => intro σ hσ _; exact ⟨σ, Exec.while_zero hσ, rfl, Frame.refl _ _⟩
  | succ n ih =>
    intro σ hσ hJ
    set σ₁ := Function.update σ 110 (σ 110 - 1) with hσ₁
    have hσ₁J : σ₁ J = 0 := by rw [hσ₁]; upd; exact hJ
    obtain ⟨σ₂, h2, -, e2t, hfr₂⟩ := runs_unconsBlock (x := 109) (h := 111) (t := 112) (b := 115)
      (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ)
      (by omegaJ) (by omegaJ) σ₁ hσ₁J
    have hσ₂J : σ₂ J = 0 := by rw [hfr₂ J (by unfold Scratch; omegaJ), hσ₁J]
    have h3 := runs_copyBlock (x := 109) (y := 112) (t := 123) (by omegaJ) (by omegaJ)
      (by omegaJ) (by omegaJ) (by omegaJ) σ₂ hσ₂J
    set σ₃ := Function.update (Function.update σ₂ 109 (σ₂ 112)) 123 0 with hσ₃
    have e3 : σ₃ 109 = (uncons (σ 109)).2 := by
      rw [hσ₃]; upd; rw [e2t, hσ₁]; upd
    have e3c : σ₃ 110 = n := by
      rw [hσ₃]; upd; rw [hfr₂ 110 (by unfold Scratch; omegaJ), hσ₁]; upd; omega
    have hσ₃J : σ₃ J = 0 := by rw [hσ₃]; upd; exact hσ₂J
    obtain ⟨σ', h', e', hfr'⟩ := ih σ₃ e3c hσ₃J
    refine ⟨σ', Exec.while_normal (by omega) (h2.seqs_cons h3.seqs_one) h', ?_, ?_⟩
    · rw [e', e3]; rfl
    · intro k hk
      rw [hfr' k hk, hσ₃]; upd
      rw [hfr₂ k (by unfold Scratch; omegaJ), hσ₁]; upd

/-- **getList**: register `8` receives `get(tape, j)`, the tape in register `7` and `j` in
register `12`. -/
theorem runs_getStmt (σ : Regs) (hJ : σ J = 0) :
    ∃ σ', Runs getStmt σ σ' ∧ σ' 8 = listGet (σ 7) (σ 12) ∧
      Frame (fun k => k = 8 ∨ (109 ≤ k ∧ k ≤ 131)) σ σ' := by
  have h1 := runs_copyBlock (x := 109) (y := 7) (t := 113) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) σ hJ
  set τ₁ := Function.update (Function.update σ 109 (σ 7)) 113 0 with hτ₁
  have hτ₁J : τ₁ J = 0 := by rw [hτ₁]; upd; exact hJ
  have h2 := runs_copyBlock (x := 110) (y := 12) (t := 114) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) τ₁ hτ₁J
  set τ₂ := Function.update (Function.update τ₁ 110 (τ₁ 12)) 114 0 with hτ₂
  have hτ₂J : τ₂ J = 0 := by rw [hτ₂]; upd; exact hτ₁J
  obtain ⟨τ₃, h3, e3, hfr₃⟩ := runs_getWalk _ τ₂ rfl hτ₂J
  have hτ₃J : τ₃ J = 0 := by rw [hfr₃ J (by omegaJ), hτ₂J]
  obtain ⟨τ₄, h4, e4h, -, hfr₄⟩ := runs_unconsBlock (x := 109) (h := 8) (t := 112) (b := 124)
    (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) τ₃ hτ₃J
  refine ⟨τ₄, h1.seqs_cons (h2.seqs_cons (h3.seqs_cons h4.seqs_one)), ?_, ?_⟩
  · rw [e4h]
    change listGet (τ₃ 109) 0 = _
    rw [e3, hτ₂, hτ₁]; upd
  · intro k hk
    simp only [not_or, not_and_or, not_le] at hk
    rw [hfr₄ k (by unfold Scratch; omegaJ), hfr₃ k (by omegaJ), hτ₂, hτ₁]; upd

/-! ### Exec -/

/-- The new value of the selected virtual register. -/
def newVal (o v : ℕ) : ℕ := if o = 1 then v + 1 else if v = 0 then v else v - 1

/-- The new virtual state. -/
def newPc (o v x y : ℕ) : ℕ := if o = 1 then x else if v = 0 then y else x

/-- **Execute**: with `o ∈ {1, 2}` in register `11`, `v` in register `8` and the targets in
registers `13, 14`. -/
theorem runs_execStmt (σ : Regs) (hJ : σ J = 0) (ho : σ 11 = 1 ∨ σ 11 = 2) :
    ∃ σ', Runs execStmt σ σ' ∧ σ' 8 = newVal (σ 11) (σ 8) ∧
      σ' 6 = newPc (σ 11) (σ 8) (σ 13) (σ 14) ∧
      Frame (fun k => k = 6 ∨ k = 8 ∨ k = 18 ∨ (132 ≤ k ∧ k ≤ 135)) σ σ' := by
  have h1 := runs_copyBlock (x := 18) (y := 11) (t := 132) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) σ hJ
  set τ₁ := Function.update (Function.update σ 18 (σ 11)) 132 0 with hτ₁
  have h2 := runs_pred 18 τ₁
  set τ₂ := Function.update τ₁ 18 (τ₁ 18 - 1) with hτ₂
  have hτ₂J : τ₂ J = 0 := by rw [hτ₂, hτ₁]; upd; exact hJ
  have hfr₂ : Frame (fun k => k = 6 ∨ k = 8 ∨ k = 18 ∨ (132 ≤ k ∧ k ≤ 135)) σ τ₂ := by
    rw [hτ₂, hτ₁]
    exact Frame.upd (Or.inr (Or.inr (Or.inl rfl))) _ (Frame.upd (Or.inr (Or.inr (Or.inr
      ⟨le_rfl, by omega⟩))) _ (Frame.upd (Or.inr (Or.inr (Or.inl rfl))) _ (Frame.refl _ _)))
  have e2o : τ₂ 18 = σ 11 - 1 := by rw [hτ₂, hτ₁]; upd
  have e2 : ∀ k, k ≠ 18 → k ≠ 132 → τ₂ k = σ k := by intro k h h'; rw [hτ₂, hτ₁]; upd
  rcases ho with ho | ho
  · -- increment
    have h3 := runs_inc (x := 8) (by omegaJ) τ₂
    set τ₃ := Function.update τ₂ 8 (τ₂ 8 + 1) with hτ₃
    have hτ₃J : τ₃ J = 0 := by rw [hτ₃]; upd; exact hτ₂J
    have h4 := runs_copyBlock (x := 6) (y := 13) (t := 135) (by omegaJ) (by omegaJ) (by omegaJ)
      (by omegaJ) (by omegaJ) τ₃ hτ₃J
    refine ⟨_, h1.seqs_cons (h2.seqs_cons (Runs.seqs_one (Exec.ifNZ_zero (by omega)
      (h3.seqs_cons h4.seqs_one)))), ?_, ?_, ?_⟩
    · upd; rw [hτ₃]; upd; rw [e2 8 (by omega) (by omega)]; simp [newVal, ho]
    · upd; rw [hτ₃]; upd; rw [e2 13 (by omega) (by omega)]; simp [newPc, ho]
    · rw [hτ₃]
      exact Frame.upd (Or.inr (Or.inr (Or.inr ⟨by omega, le_rfl⟩))) _ (Frame.upd (Or.inl rfl) _
        (Frame.upd (Or.inr (Or.inl rfl)) _ hfr₂))
  · have e8 : τ₂ 8 = σ 8 := e2 8 (by omega) (by omega)
    by_cases hv : σ 8 = 0
    · -- decrement on zero
      have h4 := runs_copyBlock (x := 6) (y := 14) (t := 134) (by omegaJ) (by omegaJ)
        (by omegaJ) (by omegaJ) (by omegaJ) τ₂ hτ₂J
      refine ⟨_, h1.seqs_cons (h2.seqs_cons (Runs.seqs_one (Exec.ifNZ_pos (by omega)
        (Exec.ifNZ_zero (by omega) h4)))), ?_, ?_, ?_⟩
      · upd; rw [e8]; simp [newVal, ho, hv]
      · upd; rw [e2 14 (by omega) (by omega)]; simp [newPc, ho, hv]
      · exact Frame.upd (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))) _ (Frame.upd (Or.inl rfl)
          _ hfr₂)
    · -- decrement
      have h3 := runs_pred 8 τ₂
      set τ₃ := Function.update τ₂ 8 (τ₂ 8 - 1) with hτ₃
      have hτ₃J : τ₃ J = 0 := by rw [hτ₃]; upd; exact hτ₂J
      have h4 := runs_copyBlock (x := 6) (y := 13) (t := 133) (by omegaJ) (by omegaJ)
        (by omegaJ) (by omegaJ) (by omegaJ) τ₃ hτ₃J
      refine ⟨_, h1.seqs_cons (h2.seqs_cons (Runs.seqs_one (Exec.ifNZ_pos (by omega)
        (Exec.ifNZ_pos (by omega) (h3.seqs_cons h4.seqs_one))))), ?_, ?_, ?_⟩
      · upd; rw [hτ₃]; upd; rw [e8]; simp [newVal, ho, hv]
      · upd; rw [hτ₃]; upd; rw [e2 13 (by omega) (by omega)]; simp [newPc, ho, hv]
      · rw [hτ₃]
        exact Frame.upd (Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))) _ (Frame.upd (Or.inl rfl)
          _ (Frame.upd (Or.inr (Or.inl rfl)) _ hfr₂))

/-! ### Set -/

/-- The save loop of `setStmt`: `n` heads of the list in register `136` move onto the saved
reversed prefix in register `138`. -/
theorem runs_saveLoop : ∀ n (σ : Regs), σ 137 = n → σ J = 0 →
    ∃ σ', Runs (whileDec 137 (seqs [unconsBlock 136 139 140 144, consBlock 139 138 138 152,
        copyBlock 136 140 163])) σ σ' ∧
      (σ' 136, σ' 138) = saveStep^[n] (σ 136, σ 138) ∧
      Frame (fun k => 136 ≤ k ∧ k ≤ 163) σ σ' := by
  intro n
  induction n with
  | zero => intro σ hσ _; exact ⟨σ, Exec.while_zero hσ, rfl, Frame.refl _ _⟩
  | succ n ih =>
    intro σ hσ hJ
    set σ₁ := Function.update σ 137 (σ 137 - 1) with hσ₁
    have hσ₁J : σ₁ J = 0 := by rw [hσ₁]; upd; exact hJ
    obtain ⟨σ₂, h2, e2h, e2t, hfr₂⟩ := runs_unconsBlock (x := 136) (h := 139) (t := 140)
      (b := 144) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ)
      (by omegaJ) (by omegaJ) (by omegaJ) σ₁ hσ₁J
    have hσ₂J : σ₂ J = 0 := by rw [hfr₂ J (by unfold Scratch; omegaJ), hσ₁J]
    obtain ⟨σ₃, h3, e3, hfr₃⟩ := runs_consBlock (h := 139) (t := 138) (out := 138) (b := 152)
      (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) σ₂ hσ₂J
    have hσ₃J : σ₃ J = 0 := by rw [hfr₃ J (by unfold Scratch; omegaJ), hσ₂J]
    have h4 := runs_copyBlock (x := 136) (y := 140) (t := 163) (by omegaJ) (by omegaJ)
      (by omegaJ) (by omegaJ) (by omegaJ) σ₃ hσ₃J
    set σ₄ := Function.update (Function.update σ₃ 136 (σ₃ 140)) 163 0 with hσ₄
    have e136 : σ₄ 136 = (uncons (σ 136)).2 := by
      rw [hσ₄]; upd; rw [hfr₃ 140 (by unfold Scratch; omegaJ), e2t, hσ₁]; upd
    have e138 : σ₄ 138 = cons (uncons (σ 136)).1 (σ 138) := by
      rw [hσ₄]; upd; rw [e3, e2h, hfr₂ 138 (by unfold Scratch; omegaJ), hσ₁]; upd
    have e137 : σ₄ 137 = n := by
      rw [hσ₄]; upd; rw [hfr₃ 137 (by unfold Scratch; omegaJ),
        hfr₂ 137 (by unfold Scratch; omegaJ), hσ₁]; upd; omega
    have hσ₄J : σ₄ J = 0 := by rw [hσ₄]; upd; exact hσ₃J
    obtain ⟨σ', h', e', hfr'⟩ := ih σ₄ e137 hσ₄J
    refine ⟨σ', Exec.while_normal (by omega) (h2.seqs_cons (h3.seqs_cons h4.seqs_one)) h', ?_, ?_⟩
    · rw [e', e136, e138, Function.iterate_succ_apply]; rfl
    · intro k hk
      simp only [not_and_or, not_le] at hk
      rw [hfr' k (by omega), hσ₄]; upd
      rw [hfr₃ k (by unfold Scratch; omegaJ), hfr₂ k (by unfold Scratch; omegaJ), hσ₁]; upd

/-- The restore loop of `setStmt`: the saved prefix in register `138` is pushed back onto the
list in register `141`; each step strictly decreases the saved prefix. -/
theorem runs_restoreLoop : ∀ (σ : Regs), σ J = 0 →
    ∃ σ', Runs (whileDec 138 (seqs [inc 138, unconsBlock 138 139 140 183,
        consBlock 139 141 141 191, copyBlock 138 140 202])) σ σ' ∧
      σ' 141 = restore (σ 138) (σ 141) ∧ Frame (fun k => 138 ≤ k ∧ k ≤ 202) σ σ' := by
  suffices ∀ n (σ : Regs), σ 138 = n → σ J = 0 →
      ∃ σ', Runs (whileDec 138 (seqs [inc 138, unconsBlock 138 139 140 183,
        consBlock 139 141 141 191, copyBlock 138 140 202])) σ σ' ∧
      σ' 141 = restore (σ 138) (σ 141) ∧ Frame (fun k => 138 ≤ k ∧ k ≤ 202) σ σ' from
    fun σ => this _ σ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ hσ hJ
    by_cases h0 : σ 138 = 0
    · exact ⟨σ, Exec.while_zero h0, by rw [h0, restore_zero], Frame.refl _ _⟩
    set σ₁ := Function.update σ 138 (σ 138 - 1) with hσ₁
    have h1 := runs_inc (x := 138) (by omegaJ) σ₁
    set σ₂ := Function.update σ₁ 138 (σ₁ 138 + 1) with hσ₂
    have hσ₂J : σ₂ J = 0 := by rw [hσ₂, hσ₁]; upd; exact hJ
    have e2 : σ₂ = σ := by rw [hσ₂, hσ₁]; regs_ext
    obtain ⟨σ₃, h3, e3h, e3t, hfr₃⟩ := runs_unconsBlock (x := 138) (h := 139) (t := 140)
      (b := 183) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ)
      (by omegaJ) (by omegaJ) (by omegaJ) σ₂ hσ₂J
    have hσ₃J : σ₃ J = 0 := by rw [hfr₃ J (by unfold Scratch; omegaJ), hσ₂J]
    obtain ⟨σ₄, h4, e4, hfr₄⟩ := runs_consBlock (h := 139) (t := 141) (out := 141) (b := 191)
      (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) σ₃ hσ₃J
    have hσ₄J : σ₄ J = 0 := by rw [hfr₄ J (by unfold Scratch; omegaJ), hσ₃J]
    have h5 := runs_copyBlock (x := 138) (y := 140) (t := 202) (by omegaJ) (by omegaJ)
      (by omegaJ) (by omegaJ) (by omegaJ) σ₄ hσ₄J
    set σ₅ := Function.update (Function.update σ₄ 138 (σ₄ 140)) 202 0 with hσ₅
    have e138 : σ₅ 138 = (uncons (σ 138)).2 := by
      rw [hσ₅]; upd; rw [hfr₄ 140 (by unfold Scratch; omegaJ), e3t, e2]
    have e141 : σ₅ 141 = cons (uncons (σ 138)).1 (σ 141) := by
      rw [hσ₅]; upd; rw [e4, e3h, hfr₃ 141 (by unfold Scratch; omegaJ), e2]
    have hσ₅J : σ₅ J = 0 := by rw [hσ₅]; upd; exact hσ₄J
    obtain ⟨σ', h', e', hfr'⟩ := ih (σ₅ 138)
      (by rw [e138, ← hσ]; exact uncons_snd_lt (Nat.pos_of_ne_zero h0)) σ₅ rfl hσ₅J
    refine ⟨σ', Exec.while_normal h0
      (h1.seqs_cons (h3.seqs_cons (h4.seqs_cons h5.seqs_one))) h', ?_, ?_⟩
    · rw [e', e138, e141, ← restore_of_ne_zero h0]
    · intro k hk
      simp only [not_and_or, not_le] at hk
      rw [hfr' k (by omega), hσ₅]; upd
      rw [hfr₄ k (by unfold Scratch; omegaJ), hfr₃ k (by unfold Scratch; omegaJ), e2]

/-- **setList**: register `7` receives `set(tape, j, v)`, with the tape in register `7`, `j`
in register `12` and `v` in register `8`. -/
theorem runs_setStmt (σ : Regs) (hJ : σ J = 0) :
    ∃ σ', Runs setStmt σ σ' ∧ σ' 7 = listSet (σ 7) (σ 12) (σ 8) ∧
      Frame (fun k => k = 7 ∨ (136 ≤ k ∧ k ≤ 203)) σ σ' := by
  have h1 := runs_copyBlock (x := 136) (y := 7) (t := 142) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) σ hJ
  set τ₁ := Function.update (Function.update σ 136 (σ 7)) 142 0 with hτ₁
  have hτ₁J : τ₁ J = 0 := by rw [hτ₁]; upd; exact hJ
  have h2 := runs_copyBlock (x := 137) (y := 12) (t := 143) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) τ₁ hτ₁J
  set τ₂ := Function.update (Function.update τ₁ 137 (τ₁ 12)) 143 0 with hτ₂
  have h3 := runs_clear 138 τ₂
  set τ₃ := Function.update τ₂ 138 0 with hτ₃
  have hτ₃J : τ₃ J = 0 := by rw [hτ₃, hτ₂, hτ₁]; upd; exact hJ
  obtain ⟨τ₄, h4, e4, hfr₄⟩ := runs_saveLoop _ τ₃ rfl hτ₃J
  have hτ₄J : τ₄ J = 0 := by rw [hfr₄ J (by omegaJ), hτ₃J]
  obtain ⟨τ₅, h5, -, e5t, hfr₅⟩ := runs_unconsBlock (x := 136) (h := 139) (t := 140) (b := 164)
    (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) τ₄ hτ₄J
  have hτ₅J : τ₅ J = 0 := by rw [hfr₅ J (by unfold Scratch; omegaJ), hτ₄J]
  obtain ⟨τ₆, h6, e6, hfr₆⟩ := runs_consBlock (h := 8) (t := 140) (out := 141) (b := 172)
    (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) τ₅ hτ₅J
  have hτ₆J : τ₆ J = 0 := by rw [hfr₆ J (by unfold Scratch; omegaJ), hτ₅J]
  obtain ⟨τ₇, h7, e7, hfr₇⟩ := runs_restoreLoop τ₆ hτ₆J
  have hτ₇J : τ₇ J = 0 := by rw [hfr₇ J (by omegaJ), hτ₆J]
  have h8 := runs_copyBlock (x := 7) (y := 141) (t := 203) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) τ₇ hτ₇J
  refine ⟨_, h1.seqs_cons (h2.seqs_cons (h3.seqs_cons (h4.seqs_cons (h5.seqs_cons
    (h6.seqs_cons (h7.seqs_cons h8.seqs_one)))))), ?_, ?_⟩
  · upd
    have e6_138 : τ₆ 138 = τ₄ 138 := by
      rw [hfr₆ 138 (by unfold Scratch; omegaJ), hfr₅ 138 (by unfold Scratch; omegaJ)]
    have e5_8 : τ₅ 8 = σ 8 := by
      rw [hfr₅ 8 (by unfold Scratch; omegaJ), hfr₄ 8 (by omegaJ), hτ₃, hτ₂, hτ₁]; upd
    have e3 : (τ₃ 136, τ₃ 138) = (σ 7, 0) := by rw [hτ₃, hτ₂, hτ₁]; upd
    have e3c : τ₃ 137 = σ 12 := by rw [hτ₃, hτ₂, hτ₁]; upd
    rw [e7, e6, e6_138, e5t, e5_8]
    have := restore_saveStep (σ 8) (σ 12) (σ 7) 0
    rw [restore_zero, ← e3, ← e3c, ← e4] at this
    rw [← e3c, ← this]
    rfl
  · intro k hk
    simp only [not_or, not_and_or, not_le] at hk
    upd
    rw [hfr₇ k (by omegaJ), hfr₆ k (by unfold Scratch; omegaJ), hfr₅ k (by unfold Scratch; omegaJ),
      hfr₄ k (by omegaJ), hτ₃, hτ₂, hτ₁]
    upd

end ZInQ.Compiler.Universal
