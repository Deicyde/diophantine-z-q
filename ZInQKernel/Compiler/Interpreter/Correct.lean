import ZInQKernel.Compiler.Interpreter.Step
import ZInQKernel.Compiler.Universal.Shape

/-!
# Correctness of the universal interpreter

For all `e, n`: the interpreter `𝒰` accepts `(e, n)` (reaches its final halt with all
registers zero) exactly when the program numbered `e` halts on `n`.

If `w = 0` the decoding step exits to cleanup and `μ_e` halts at once. Otherwise decoding and
initialization reach a configuration coherent with the initial virtual configuration. If the
virtual run halts, finitely many loop iterations reach a coherent configuration at a halting
virtual state, from which cleanup is entered; cleanup clears every register and halts. If the
virtual run never halts, the loop iterations give coherent configurations at arbitrarily late
times, so the run of `𝒰` never stops; in particular it never reaches its final halt. (The
interpreter is deterministic, so no separate argument about entries into cleanup is needed.)

(Blueprint: `compiler/natural/universal/interpreter-correct.md`.)
-/

namespace ZInQ.Compiler.Universal

open RM Stmt

/-! ### Decoding and initialization -/

theorem uncons_succ (e : ℕ) : uncons (e + 1) = split2 e := by
  have h : e + 1 = cons (split2 e).1 (split2 e).2 := split2_spec e
  rw [h, uncons_cons]

theorem initStmt_writes_lt : ∀ k ∈ initStmt.writes, k < 204 := by decide +kernel

/-- **Decoding and initialization.** From a file with `e` in register `0`, `n` in register `1`
and the jump register zero: if `w = 0` the statement exits to cleanup; otherwise it completes
with `w, D, β = 2 ^ w, pc = 0` and the tape `cons(n, nil)` in registers `3, …, 7`. -/
theorem exec_initStmt (ρ : Regs) (hJ : ρ J = 0) :
    ((split2 (ρ 0)).1 = 0 → ∃ ρ', Exec initStmt ρ (.exit ρ')) ∧
    ((split2 (ρ 0)).1 ≠ 0 → ∃ ρ', Runs initStmt ρ ρ' ∧ ρ' 3 = (split2 (ρ 0)).1 ∧
      ρ' 4 = (split2 (ρ 0)).2 ∧ ρ' 5 = 2 ^ (split2 (ρ 0)).1 ∧ ρ' 6 = 0 ∧
      ρ' 7 = cons (ρ 1) 0) := by
  have h1 := runs_copyBlock (x := 17) (y := 0) (t := 19) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) ρ hJ
  set τ₁ := Function.update (Function.update ρ 17 (ρ 0)) 19 0 with hτ₁
  have h2 := runs_inc (x := 17) (by omegaJ) τ₁
  set τ₂ := Function.update τ₁ 17 (τ₁ 17 + 1) with hτ₂
  have hτ₂J : τ₂ J = 0 := by rw [hτ₂, hτ₁]; upd; exact hJ
  obtain ⟨τ₃, h3, e3w, e3D, hfr₃⟩ := runs_unconsBlock (x := 17) (h := 3) (t := 4) (b := 20)
    (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) τ₂ hτ₂J
  have e17 : τ₂ 17 = ρ 0 + 1 := by rw [hτ₂, hτ₁]; upd
  rw [e17, uncons_succ] at e3w e3D
  have hτ₃J : τ₃ J = 0 := by rw [hfr₃ J (by unfold Scratch; omegaJ), hτ₂J]
  refine ⟨fun hw => ⟨τ₃, Exec.seqs_cons h1 (Exec.seqs_cons h2 (Exec.seqs_cons h3
    (Exec.seqs_abnormal (Exec.ifNZ_zero (by rw [e3w, hw]) (Exec.exit _)) trivial)))⟩,
    fun hw => ?_⟩
  have h4 : Runs (ifNZ 3 skip exit) τ₃ τ₃ := Exec.ifNZ_pos (by rw [e3w]; exact hw) (Exec.skip _)
  have h5 := runs_clear 5 τ₃
  set τ₅ := Function.update τ₃ 5 0 with hτ₅
  have h6 := runs_inc (x := 5) (by omegaJ) τ₅
  set τ₆ := Function.update τ₅ 5 (τ₅ 5 + 1) with hτ₆
  have hτ₆J : τ₆ J = 0 := by rw [hτ₆, hτ₅]; upd; exact hτ₃J
  have h7 := runs_copyBlock (x := 10) (y := 3) (t := 28) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) τ₆ hτ₆J
  set τ₇ := Function.update (Function.update τ₆ 10 (τ₆ 3)) 28 0 with hτ₇
  have hτ₇J : τ₇ J = 0 := by rw [hτ₇]; upd; exact hτ₆J
  obtain ⟨τ₈, h8, e8, -, hfr₈⟩ := runs_doubleLoop (c := 10) (x := 5) (s := 29) (t₁ := 30)
    (t₂ := 31) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ)
    (by omegaJ) τ₇ hτ₇J
  have hτ₈J : τ₈ J = 0 := by rw [hfr₈ J (by omegaJ), hτ₇J]
  have h9 := runs_clear 6 τ₈
  set τ₉ := Function.update τ₈ 6 0 with hτ₉
  have hτ₉J : τ₉ J = 0 := by rw [hτ₉]; upd; exact hτ₈J
  obtain ⟨τ₁₀, h10, e10, hfr₁₀⟩ := runs_consBlock (h := 1) (t := J) (out := 7) (b := 32)
    (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) (by omegaJ) τ₉ hτ₉J
  have hrun : Runs initStmt ρ τ₁₀ :=
    h1.seqs_cons (h2.seqs_cons (h3.seqs_cons (h4.seqs_cons (h5.seqs_cons (h6.seqs_cons
      (h7.seqs_cons (h8.seqs_cons (h9.seqs_cons h10.seqs_one))))))))
  -- frames of the later blocks
  have f10 : ∀ k, k ≠ 7 → (k < 32 ∨ 42 < k) → τ₁₀ k = τ₉ k :=
    fun k a b => hfr₁₀ k (by unfold Scratch; omega)
  have f8 : ∀ k, k ≠ 10 → k ≠ 5 → k ≠ 29 → k ≠ 30 → k ≠ 31 → τ₈ k = τ₇ k :=
    fun k a b c d e => hfr₈ k (by omega)
  have g3 : ∀ k, k = 3 ∨ k = 4 → τ₁₀ k = τ₃ k := by
    intro k hk
    rw [f10 k (by omega) (by omega), hτ₉]; upd
    rw [f8 k (by omega) (by omega) (by omega) (by omega) (by omega), hτ₇, hτ₆, hτ₅]; upd
  refine ⟨τ₁₀, hrun, ?_, ?_, ?_, ?_, ?_⟩
  · rw [g3 3 (Or.inl rfl), e3w]
  · rw [g3 4 (Or.inr rfl), e3D]
  · rw [f10 5 (by omega) (by omega), hτ₉]; upd
    rw [e8, hτ₇]; upd
    rw [hτ₆, hτ₅]; upd
    rw [e3w]; simp
  · rw [f10 6 (by omega) (by omega), hτ₉]; upd
  · rw [e10, hτ₉]; upd
    rw [hτ₈J, f8 1 (by omega) (by omega) (by omega) (by omega) (by omega), hτ₇, hτ₆, hτ₅]
    upd
    rw [hfr₃ 1 (by unfold Scratch; omegaJ), hτ₂, hτ₁]; upd

/-! ### Cleanup -/

theorem runs_clears : ∀ (n : ℕ) (ρ : Regs),
    Runs (seqs ((List.range n).map clear)) ρ (fun k => if k < n then 0 else ρ k)
  | 0, ρ => by simpa using runs_seqs_nil ρ
  | n + 1, ρ => by
    rw [List.range_succ, List.map_append]
    refine ((runs_clears n ρ).seqs_append (runs_clear n _).seqs_one).of_eq ?_
    funext k
    simp only [Function.update_apply]
    split_ifs <;> omega

/-- **Cleanup** clears registers `0, …, 203`. -/
theorem runs_cleanupStmt (ρ : Regs) :
    Runs cleanupStmt ρ (fun k => if k < 204 then 0 else ρ k) := runs_clears 204 ρ

theorem interpreter_toMachine_last : interpreter.toMachine 1398 = .halt := by
  simp [Program.toMachine, List.getD_eq_getElem?_getD, interpreter_getElem?_last]

/-- From the cleanup entry, with every register from `204` on zero, the interpreter accepts. -/
theorem accepts_of_reaches_cleanup {a : Fin 2 → ℕ} {ρ : Regs}
    (h : Reaches interpreter.toMachine ⟨0, initFile a⟩ ⟨cleanupEntry, ρ⟩) (hJ : ρ J = 0)
    (hhigh : ∀ k, 204 ≤ k → ρ k = 0) : interpreter.Accepts a := by
  obtain ⟨t₁, h₁⟩ := h
  obtain ⟨t₂, h₂⟩ := (runs_cleanupStmt ρ).reaches codeAt_cleanupStmt hJ
  refine ⟨t₁ + t₂, _, by rw [stepN_add, h₁]; exact h₂, ?_, fun k => ?_⟩
  · rw [cleanupStmt_size, interpreter_length]
  · simp only
    split_ifs with hk
    · rfl
    · exact hhigh _ (by omega)

/-- A run that has stopped stays stopped. -/
theorem stepN_eq_none_of_halt {μ : Machine} {c₀ c : Config} {T : ℕ}
    (h : stepN μ T c₀ = some c) (hc : μ c.state = .halt) :
    ∀ t, T < t → stepN μ t c₀ = none := by
  intro t ht
  obtain ⟨d, rfl⟩ : ∃ d, t = T + (d + 1) := ⟨t - T - 1, by omega⟩
  rw [stepN_add, h]
  simp [stepN_succ, (step_eq_none_iff μ c).mpr hc]

/-! ### Correctness -/

/-- The initial file of the interpreter on `(e, n)`. -/
theorem initFile_two (e n : ℕ) :
    initFile ![e, n] 0 = e ∧ initFile ![e, n] 1 = n ∧ ∀ k, 2 ≤ k → initFile ![e, n] k = 0 :=
  ⟨rfl, rfl, fun _ hk => initFile_of_le _ hk⟩

theorem represents_init (n : ℕ) : Represents (initFile ![n]) (cons n 0) := by
  intro i
  rcases i with _ | i
  · simp [initFile]
  · simp [listGet_zero_left, initFile_of_le _ (show 1 ≤ i + 1 by omega)]

/-- Decoding and initialization reach a coherent configuration (or cleanup, if `w = 0`). -/
theorem interpreter_init (e n : ℕ) :
    ((split2 e).1 = 0 → ∃ ρ', Reaches interpreter.toMachine ⟨0, initFile ![e, n]⟩
      ⟨cleanupEntry, ρ'⟩ ∧ ρ' J = 0 ∧ ∀ k, 204 ≤ k → ρ' k = 0) ∧
    ((split2 e).1 ≠ 0 → ∃ σ, Reaches interpreter.toMachine ⟨0, initFile ![e, n]⟩ σ ∧
      Coherent e ⟨0, initFile ![n]⟩ σ) := by
  obtain ⟨h0, h1, hk⟩ := initFile_two e n
  have hJ : initFile ![e, n] J = 0 := hk J (by decide)
  obtain ⟨hexit, hrun⟩ := exec_initStmt (initFile ![e, n]) hJ
  rw [h0] at hexit hrun
  have hhigh : ∀ (ρ' : Regs) (o : Outcome), Exec initStmt (initFile ![e, n]) o → o.regs = ρ' →
      ∀ k, 204 ≤ k → ρ' k = 0 := by
    intro ρ' o hex ho k hk'
    rw [← ho, Exec.regs_of_not_mem_writes hex k (fun hm => by
      have := initStmt_writes_lt k hm; omega), hk k (by omega)]
  refine ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨ρ', hex⟩ := hexit hw
    exact ⟨ρ', compile_correct hex codeAt_initStmt hJ, hex.regs_J hJ, hhigh ρ' _ hex rfl⟩
  · obtain ⟨ρ', hr, e3, e4, e5, e6, e7⟩ := hrun hw
    refine ⟨⟨loopStart, ρ'⟩, ?_, rfl, ⟨hw, e3, e4, e5, e6, ?_, hr.regs_J hJ, hhigh ρ' _ hr rfl⟩⟩
    · have := hr.reaches codeAt_initStmt hJ
      rwa [initStmt_size] at this
    · show Represents (initFile ![n]) (ρ' 7)
      rw [e7, h1]; exact represents_init n

/-- **Correctness of the universal interpreter.** `𝒰` accepts `(e, n)` exactly when the program
numbered `e` halts on `n`. -/
theorem interpreter_accepts_iff (e n : ℕ) : interpreter.Accepts ![e, n] ↔ halts e n := by
  obtain ⟨hinit0, hinit⟩ := interpreter_init e n
  constructor
  · -- acceptance implies virtual halting
    intro hacc
    by_contra hnot
    have hw : (split2 e).1 ≠ 0 := by
      intro hw
      exact hnot ⟨0, _, rfl, decodeMachine_of_w_eq_zero hw _⟩
    obtain ⟨σ₀, ⟨t₀, ht₀⟩, hcoh₀⟩ := hinit hw
    -- coherent configurations at arbitrarily late times
    have key : ∀ m, ∃ t vc σ, m ≤ t ∧
        stepN interpreter.toMachine t ⟨0, initFile ![e, n]⟩ = some σ ∧ Coherent e vc σ ∧
        ∃ tv, stepN (decodeMachine e) tv ⟨0, initFile ![n]⟩ = some vc := by
      intro m
      induction m with
      | zero => exact ⟨t₀, _, σ₀, Nat.zero_le _, ht₀, hcoh₀, 0, rfl⟩
      | succ m ih =>
        obtain ⟨t, vc, σ, hm, ht, hcoh, tv, hv⟩ := ih
        have hnh : decodeMachine e vc.state ≠ .halt := fun hh => hnot ⟨tv, vc, hv, hh⟩
        obtain ⟨vc', hvc'⟩ : ∃ vc', step (decodeMachine e) vc = some vc' := by
          cases hs : step (decodeMachine e) vc with
          | none => exact absurd ((step_eq_none_iff _ _).mp hs) hnh
          | some vc' => exact ⟨vc', rfl⟩
        obtain ⟨t', σ', ht', hcoh', -⟩ := (interpreter_step hcoh).2 vc' hvc'
        refine ⟨t + (t' + 1), vc', σ', by omega, by rw [stepN_add, ht]; exact ht', hcoh',
          tv + 1, by rw [stepN_succ', hv]; exact hvc'⟩
    obtain ⟨T, c, hT, hc, -⟩ := hacc
    obtain ⟨t, vc, σ, hm, ht, -, -⟩ := key (T + 1)
    have hhalt : interpreter.toMachine c.state = .halt := by
      rw [hc, interpreter_length]; exact interpreter_toMachine_last
    rw [stepN_eq_none_of_halt hT hhalt t (by omega)] at ht
    cases ht
  · -- virtual halting implies acceptance
    rintro ⟨tv, c, hv, hc⟩
    by_cases hw : (split2 e).1 = 0
    · obtain ⟨ρ', hr, hJ, hhigh⟩ := hinit0 hw
      exact accepts_of_reaches_cleanup hr hJ hhigh
    obtain ⟨σ₀, hr₀, hcoh₀⟩ := hinit hw
    suffices ∀ tv (vc σ : Config), Coherent e vc σ →
        stepN (decodeMachine e) tv vc = some c →
        ∃ ρ', Reaches interpreter.toMachine σ ⟨cleanupEntry, ρ'⟩ ∧ ρ' J = 0 ∧
          ∀ k, 204 ≤ k → ρ' k = 0 by
      obtain ⟨ρ', hr, hJ, hhigh⟩ := this tv _ σ₀ hcoh₀ hv
      exact accepts_of_reaches_cleanup (hr₀.trans hr) hJ hhigh
    intro tv
    induction tv with
    | zero =>
      intro vc σ hcoh hvc
      cases hvc
      exact (interpreter_step hcoh).1 hc
    | succ tv ih =>
      intro vc σ hcoh hvc
      rw [stepN_succ] at hvc
      cases hs : step (decodeMachine e) vc with
      | none => rw [hs] at hvc; cases hvc
      | some vc' =>
        rw [hs] at hvc
        obtain ⟨t', σ', ht', hcoh', -⟩ := (interpreter_step hcoh).2 vc' hs
        obtain ⟨ρ', hr, hJ, hhigh⟩ := ih vc' σ' hcoh' hvc
        exact ⟨ρ', Reaches.trans ⟨t' + 1, ht'⟩ hr, hJ, hhigh⟩

end ZInQ.Compiler.Universal
