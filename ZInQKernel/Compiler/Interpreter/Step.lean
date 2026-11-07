import ZInQKernel.Compiler.Interpreter.Phases
import ZInQKernel.Compiler.Interpreter.Numbering

/-!
# One interpreter loop simulates one instruction

A configuration of the interpreter `𝒰` is *coherent* with a virtual configuration `(i, ρ)` of
`μ_e` when it is at the entry of the main loop (state `165`), registers `3, 4, 5` hold `w ≥ 1`,
`D` and `β = 2 ^ w` of `e`, register `6` holds `pc = i`, register `7` holds a list code
representing `ρ`, the jump register is zero and every register from `204` on is zero. From a
coherent configuration, if `μ_e(i) = halt` the run reaches the cleanup entry (state `1194`);
otherwise it returns, after at least one step, to a configuration coherent with the successor
of `(i, ρ)`.

(Blueprint: `compiler/natural/universal/interpreter-step.md`.)
-/

namespace ZInQ.Compiler.Universal

open RM Stmt

/-- The entry of the main loop. -/
abbrev loopStart : ℕ := 165

/-- The register part of coherence. Scratch registers may hold anything (every block clears its
scratch registers before use); registers from `204` on are zero. -/
structure CoherentRegs (e : ℕ) (vc : Config) (ρ : Regs) : Prop where
  w_pos : (split2 e).1 ≠ 0
  w : ρ 3 = (split2 e).1
  D : ρ 4 = (split2 e).2
  β : ρ 5 = 2 ^ (split2 e).1
  pc : ρ 6 = vc.state
  tape : Represents vc.regs (ρ 7)
  J : ρ J = 0
  high : ∀ k, 204 ≤ k → ρ k = 0

/-- Coherence of a configuration of `𝒰` with a virtual configuration of `μ_e`. -/
def Coherent (e : ℕ) (vc σ : Config) : Prop := σ.state = loopStart ∧ CoherentRegs e vc σ.regs

theorem stepStmt_writes_lt : ∀ k ∈ stepStmt.writes, k < 204 := by decide +kernel

theorem decodeInstr_eq_halt {o j x y : ℕ} (h1 : o ≠ 1) (h2 : o ≠ 2) :
    decodeInstr o j x y = .halt := by simp [decodeInstr, h1, h2]

/-- The digits read by the fetch phase are those of the numbering. -/
theorem div_pow_mod_eq_digit (w D t : ℕ) : D / (2 ^ w) ^ t % 2 ^ w = digit w D t := by
  rw [digit, pow_mul]

/-- **One loop iteration, semantically.** -/
theorem exec_stepStmt {e : ℕ} {vc : Config} {ρ : Regs} (h : CoherentRegs e vc ρ) :
    (decodeMachine e vc.state = .halt → ∃ ρ', Exec stepStmt ρ (.exit ρ')) ∧
    (∀ vc', step (decodeMachine e) vc = some vc' →
      ∃ ρ', Runs stepStmt ρ ρ' ∧ CoherentRegs e vc' ρ') := by
  obtain ⟨hw, h3, h4, h5, h6, h7, hJ, hhigh⟩ := h
  have hβ : 0 < ρ 5 := by rw [h5]; positivity
  obtain ⟨σ₁, r1, e11, e12, e13, e14, hfr₁⟩ := runs_fetchStmt ρ hJ hβ
  have hσ₁J : σ₁ J = 0 := r1.regs_J hJ
  set w := (split2 e).1
  set D := (split2 e).2
  have hdec : decodeMachine e vc.state = decodeInstr (σ₁ 11) (σ₁ 12) (σ₁ 13) (σ₁ 14) := by
    rw [decodeMachine_of_w_ne_zero hw, e11, e12, e13, e14, h4, h5, h6,
      div_pow_mod_eq_digit, div_pow_mod_eq_digit, div_pow_mod_eq_digit, div_pow_mod_eq_digit]
  by_cases hop : σ₁ 11 = 1 ∨ σ₁ 11 = 2
  · refine ⟨fun hh => ?_, fun vc' hstep => ?_⟩
    · rw [hdec] at hh
      rcases hop with hop | hop <;> simp [decodeInstr, hop] at hh
    obtain ⟨σ₂, r2, hfr₂⟩ := runs_opcodeStmt σ₁ hσ₁J hop
    have hσ₂J : σ₂ J = 0 := r2.regs_J hσ₁J
    obtain ⟨σ₃, r3, e38, hfr₃⟩ := runs_getStmt σ₂ hσ₂J
    have hσ₃J : σ₃ J = 0 := r3.regs_J hσ₂J
    have hop₃ : σ₃ 11 = 1 ∨ σ₃ 11 = 2 := by
      rw [hfr₃ 11 (by omega), hfr₂ 11 (by omega)]; exact hop
    obtain ⟨σ₄, r4, e48, e46, hfr₄⟩ := runs_execStmt σ₃ hσ₃J hop₃
    have hσ₄J : σ₄ J = 0 := r4.regs_J hσ₃J
    obtain ⟨σ₅, r5, e57, hfr₅⟩ := runs_setStmt σ₄ hσ₄J
    have hrun : Runs stepStmt ρ σ₅ :=
      r1.seqs_cons (r2.seqs_cons (r3.seqs_cons (r4.seqs_cons r5.seqs_one)))
    -- the registers read along the way
    have f2 : ∀ k, k ≠ 18 → k ≠ 108 → σ₂ k = σ₁ k := fun k a b => hfr₂ k (by omega)
    have f3 : ∀ k, k ≠ 8 → (k < 109 ∨ 131 < k) → σ₃ k = σ₂ k := fun k a b => hfr₃ k (by omega)
    have f4 : ∀ k, k ≠ 6 → k ≠ 8 → k ≠ 18 → (k < 132 ∨ 135 < k) → σ₄ k = σ₃ k :=
      fun k a b c d => hfr₄ k (by omega)
    have f5 : ∀ k, k ≠ 7 → (k < 136 ∨ 203 < k) → σ₅ k = σ₄ k := fun k a b => hfr₅ k (by omega)
    have f1 : ∀ k, (k < 9 ∨ (16 < k ∧ k < 43) ∨ 107 < k) → σ₁ k = ρ k :=
      fun k a => hfr₁ k (by omega)
    have g11 : σ₃ 11 = σ₁ 11 := by rw [f3 11 (by omega) (by omega), f2 11 (by omega) (by omega)]
    have g12 : σ₄ 12 = σ₁ 12 := by
      rw [f4 12 (by omega) (by omega) (by omega) (by omega), f3 12 (by omega) (by omega),
        f2 12 (by omega) (by omega)]
    have g13 : σ₃ 13 = σ₁ 13 := by rw [f3 13 (by omega) (by omega), f2 13 (by omega) (by omega)]
    have g14 : σ₃ 14 = σ₁ 14 := by rw [f3 14 (by omega) (by omega), f2 14 (by omega) (by omega)]
    have g7 : ∀ k, k ≠ 6 → k ≠ 7 → k ≠ 8 → k < 9 → σ₅ k = ρ k := by
      intro k a b c d
      rw [f5 k b (by omega), f4 k a c (by omega) (by omega), f3 k c (by omega),
        f2 k (by omega) (by omega), f1 k (by omega)]
    have g7' : σ₄ 7 = ρ 7 := by
      rw [f4 7 (by omega) (by omega) (by omega) (by omega), f3 7 (by omega) (by omega),
        f2 7 (by omega) (by omega), f1 7 (by omega)]
    have g2 : σ₂ 12 = σ₁ 12 := f2 12 (by omega) (by omega)
    have g2' : σ₂ 7 = ρ 7 := by rw [f2 7 (by omega) (by omega), f1 7 (by omega)]
    have hv : σ₃ 8 = vc.regs (σ₁ 12) := by rw [e38, g2', g2, h7]
    have hhigh₅ : ∀ k, 204 ≤ k → σ₅ k = 0 := by
      intro k hk
      rw [hrun.frame k (fun hm => by have := stepStmt_writes_lt k hm; omega), hhigh k hk]
    -- the virtual step
    have hcoh : ∀ (vc' : Config), vc'.state = newPc (σ₁ 11) (vc.regs (σ₁ 12)) (σ₁ 13) (σ₁ 14) →
        Represents vc'.regs (listSet (ρ 7) (σ₁ 12) (newVal (σ₁ 11) (vc.regs (σ₁ 12)))) →
        CoherentRegs e vc' σ₅ := by
      intro vc' hs hr
      refine ⟨hw, ?_, ?_, ?_, ?_, ?_, r5.regs_J hσ₄J, hhigh₅⟩
      · rw [g7 3 (by omega) (by omega) (by omega) (by omega), h3]
      · rw [g7 4 (by omega) (by omega) (by omega) (by omega), h4]
      · rw [g7 5 (by omega) (by omega) (by omega) (by omega), h5]
      · rw [f5 6 (by omega) (by omega), e46, hs, g11, g13, g14, hv]
      · rw [e57, g7', g12, e48, g11, hv]; exact hr
    refine ⟨σ₅, hrun, ?_⟩
    unfold step at hstep
    rw [hdec] at hstep
    rcases hop with hop | hop
    · simp only [decodeInstr, hop, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      refine hcoh _ (by simp [newPc, hop]) ?_
      simp only [newVal, hop, ↓reduceIte]
      exact h7.update _ _
    · simp only [decodeInstr, hop, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte] at hstep
      by_cases hz : vc.regs (σ₁ 12) = 0
      · simp only [hz, ↓reduceIte, Option.some.injEq] at hstep
        subst hstep
        refine hcoh _ (by simp [newPc, hop, hz]) ?_
        have := h7.update (σ₁ 12) 0
        rw [Function.update_eq_self_iff.mpr hz.symm] at this
        rw [show newVal (σ₁ 11) (vc.regs (σ₁ 12)) = 0 by simp [newVal, hop, hz]]
        exact this
      · simp only [hz, ↓reduceIte, Option.some.injEq] at hstep
        subst hstep
        refine hcoh _ (by simp [newPc, hop, hz]) ?_
        simp only [newVal, hop, hz, show (2 : ℕ) ≠ 1 by decide, ↓reduceIte]
        exact h7.update _ _
  · have hhalt : decodeMachine e vc.state = .halt := by
      rw [hdec]; push Not at hop; exact decodeInstr_eq_halt hop.1 hop.2
    refine ⟨fun _ => ?_, fun vc' hstep => ?_⟩
    · push Not at hop
      obtain ⟨σ₂, r2⟩ := exec_opcodeStmt_exit σ₁ hσ₁J hop.1 hop.2
      exact ⟨σ₂, Exec.seqs_cons r1 (Exec.seqs_abnormal r2 trivial)⟩
    · rw [(step_eq_none_iff _ _).mpr hhalt] at hstep
      cases hstep

/-! ### The code of the interpreter -/

theorem codeAt_toMachine (p : Program) : CodeAt p.toMachine 0 p := fun k hk => by
  rw [Nat.zero_add, toMachine_of_lt p hk]

theorem codeAt_interpreter :
    CodeAt interpreter.toMachine 0 ((seq mainStmt cleanupStmt).compile 0 0 0 cleanupEntry) := by
  have h : CodeAt interpreter.toMachine 0 interpreterCode := by
    rw [← interpreter_eq_compile]; exact codeAt_toMachine _
  exact h.append_left

theorem codeAt_main :
    CodeAt interpreter.toMachine 0
      ((seq initStmt (seq (loop bodyStmt) skip)).compile 0 0 0 cleanupEntry) :=
  codeAt_interpreter.seq.1

theorem codeAt_initStmt : CodeAt interpreter.toMachine 0 (initStmt.compile 0 0 0 cleanupEntry) :=
  codeAt_main.seq.1

theorem codeAt_body :
    CodeAt interpreter.toMachine loopStart
      (bodyStmt.compile loopStart loopStart (loopStart + bodyStmt.size) cleanupEntry) := by
  have h := codeAt_main.seq.2.seq.1
  rw [Nat.zero_add, initStmt_size] at h
  exact h

theorem codeAt_stepStmt :
    CodeAt interpreter.toMachine loopStart
      (stepStmt.compile loopStart loopStart (loopStart + bodyStmt.size) cleanupEntry) :=
  codeAt_body.seq.1

theorem interpreter_toMachine_cont :
    interpreter.toMachine (loopStart + 1028) = .dec J loopStart loopStart := by
  have h := codeAt_body.seq.2
  rw [stepStmt_size] at h
  exact h.get 0 (by simp [Stmt.compile])

theorem codeAt_cleanupStmt :
    CodeAt interpreter.toMachine cleanupEntry
      (cleanupStmt.compile cleanupEntry 0 0 cleanupEntry) := by
  have h := codeAt_interpreter.seq.2
  rw [Nat.zero_add, mainStmt_size] at h
  exact h

/-! ### One loop iteration of the machine -/

/-- **One interpreter loop simulates one instruction.** From a configuration coherent with
`(i, ρ)`: if `μ_e(i) = halt` the run reaches the cleanup entry, with the jump register and every
register from `204` on zero; otherwise it returns, after at least one step and without passing
through cleanup (every configuration before the return is at a state of the main loop), to a
configuration coherent with the successor of `(i, ρ)`. -/
theorem interpreter_step {e : ℕ} {vc σ : Config} (h : Coherent e vc σ) :
    (decodeMachine e vc.state = .halt →
      ∃ ρ', Reaches interpreter.toMachine σ ⟨cleanupEntry, ρ'⟩ ∧ ρ' J = 0 ∧
        ∀ k, 204 ≤ k → ρ' k = 0) ∧
    (∀ vc', step (decodeMachine e) vc = some vc' →
      ∃ t σ', stepN interpreter.toMachine (t + 1) σ = some σ' ∧ Coherent e vc' σ' ∧
        ∀ t' ≤ t, ∃ d, stepN interpreter.toMachine t' σ = some d ∧
          loopStart ≤ d.state ∧ d.state < cleanupEntry) := by
  obtain ⟨hs, hc⟩ := h
  obtain ⟨hhalt, hnext⟩ := exec_stepStmt hc
  obtain ⟨σs, σρ⟩ := σ
  simp only at hs
  subst hs
  refine ⟨fun hh => ?_, fun vc' hstep => ?_⟩
  · obtain ⟨ρ', hex⟩ := hhalt hh
    refine ⟨ρ', compile_correct hex codeAt_stepStmt hc.J, hex.regs_J hc.J, fun k hk => ?_⟩
    have := Exec.regs_of_not_mem_writes hex k
      (fun hm => by have := stepStmt_writes_lt k hm; omega)
    rw [show (Outcome.exit ρ').regs = ρ' from rfl] at this
    rw [this, hc.high k hk]
  · obtain ⟨ρ', hrun, hc'⟩ := hnext vc' hstep
    obtain ⟨t, ht, hin⟩ := compile_correct_in hrun codeAt_stepStmt hc.J
    simp only [Outcome.target, Outcome.regs, stepStmt_size] at ht
    refine ⟨t, ⟨loopStart, ρ'⟩, ?_, ⟨rfl, hc'⟩, fun t' ht' => ?_⟩
    · rw [stepN_succ', ht]
      simp [step, interpreter_toMachine_cont, hc'.J]
    · rcases Nat.lt_or_eq_of_le ht' with ht' | rfl
      · obtain ⟨d, hd, hS⟩ := hin t' ht'
        simp only [Stmt.Range, stepStmt_size] at hS
        have e1 : loopStart = 165 := rfl
        have e2 : cleanupEntry = 1194 := rfl
        exact ⟨d, hd, hS.1, by omega⟩
      · exact ⟨_, ht, by simp, by simp⟩

end ZInQ.Compiler.Universal
