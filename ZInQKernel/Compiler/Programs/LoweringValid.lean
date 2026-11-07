import ZInQKernel.Compiler.Programs.Lowering

/-!
# Validity of the lowering

Blueprint: `compiler/natural/programs/lowering.md`.

`low(S)` is a primitive program valid for its register count `r = J + 7`: its last
instruction is the only halt, register indices are below `r` and targets below the length.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace ZInQ.Compiler.IR

open RM

/-- Instructions with register indices below `r` and targets below `m` (halt excluded). -/
theorem assignB_valid {J x : ℕ} {o : Op} {s m : ℕ} (hx : x < J) (ho : o.RegsBelow J)
    (hm : s + o.len < m) : ∀ ins ∈ assignB J x o s, ins.Valid (J + 7) m := by
  intro ins h
  cases o with
  | const k =>
    simp only [Op.len] at hm
    simp only [assignB, clearB, incs, List.mem_append, List.mem_cons, List.mem_map,
      List.mem_range, List.mem_nil_iff, or_false] at h
    rcases h with rfl | ⟨i, hi, rfl⟩ <;> simp only [Instr.Valid, aux] <;> omega
  | copy y =>
    simp only [Op.len, Op.RegsBelow] at hm ho
    simp only [assignB, snap, clearB, transfer1, transfer2, jmp, List.mem_append, List.mem_cons,
      List.mem_nil_iff, or_false] at h
    casesm* _ ∨ _ <;> subst_vars <;> simp only [Instr.Valid, aux] <;> omega
  | add y z | sub y z | mul y z =>
    simp only [Op.len, Op.RegsBelow] at hm ho
    simp only [assignB, snap2, snap, clearB, transfer1, transfer2, jmp, List.mem_append,
      List.mem_cons, List.mem_nil_iff, or_false] at h
    casesm* _ ∨ _ <;> subst_vars <;> simp only [Instr.Valid, aux] <;> omega
  | div y z | mod y z =>
    simp only [Op.len, Op.RegsBelow] at hm ho
    simp only [assignB, divModB, snap2, snap, clearB, transfer1, transfer2, jmp, List.mem_append,
      List.mem_cons, List.mem_nil_iff, or_false, Bool.false_eq_true, ite_true, ite_false,
      List.length_cons, List.length_nil] at h
    casesm* _ ∨ _ <;> subst_vars <;> simp only [Instr.Valid, aux] <;> omega

theorem code_valid {J : ℕ} : ∀ (S : Stmt) {s acc rej m : ℕ}, S.RegsBelow J → s + S.len < m →
    acc < m → rej < m → ∀ ins ∈ code J S s acc rej, ins.Valid (J + 7) m
  | .assign x o, s, acc, rej, m, hS, hm, _, _ => assignB_valid hS.1 hS.2 hm
  | .seq S T, s, acc, rej, m, hS, hm, ha, hr => by
    intro ins h
    simp only [code, List.mem_append] at h
    simp only [Stmt.len] at hm
    rcases h with h | h
    · exact code_valid S hS.1 (by omega) ha hr ins h
    · exact code_valid T hS.2 (by omega) ha hr ins h
  | .ifLt y z S T, s, acc, rej, m, hS, hm, ha, hr => by
    intro ins h
    obtain ⟨hy, hz, h1, h2⟩ := hS
    simp only [Stmt.len] at hm
    simp only [code, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with ((h | h) | h) | h
    · simp only [ltTest, snap2, snap, transfer1, transfer2, jmp, List.mem_append, List.mem_cons,
        List.mem_nil_iff, or_false] at h
      casesm* _ ∨ _ <;> subst_vars <;> simp only [Instr.Valid, aux] <;> omega
    · exact code_valid S h1 (by omega) ha hr ins h
    · subst h; simp only [jmp, Instr.Valid]; omega
    · exact code_valid T h2 (by omega) ha hr ins h
  | .ifEq y z S T, s, acc, rej, m, hS, hm, ha, hr => by
    intro ins h
    obtain ⟨hy, hz, h1, h2⟩ := hS
    simp only [Stmt.len] at hm
    simp only [code, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with ((h | h) | h) | h
    · simp only [eqTest, snap2, snap, transfer1, transfer2, jmp, List.mem_append, List.mem_cons,
        List.mem_nil_iff, or_false] at h
      casesm* _ ∨ _ <;> subst_vars <;> simp only [Instr.Valid, aux] <;> omega
    · exact code_valid S h1 (by omega) ha hr ins h
    · subst h; simp only [jmp, Instr.Valid]; omega
    · exact code_valid T h2 (by omega) ha hr ins h
  | .whileLt y z S, s, acc, rej, m, hS, hm, ha, hr => by
    intro ins h
    obtain ⟨hy, hz, h1⟩ := hS
    simp only [Stmt.len] at hm
    simp only [code, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h
    rcases h with (h | h) | h
    · simp only [ltTest, snap2, snap, transfer1, transfer2, jmp, List.mem_append, List.mem_cons,
        List.mem_nil_iff, or_false] at h
      casesm* _ ∨ _ <;> subst_vars <;> simp only [Instr.Valid, aux] <;> omega
    · exact code_valid S h1 (by omega) ha hr ins h
    · subst h; simp only [jmp, Instr.Valid]; omega
  | .accept, s, acc, rej, m, _, _, ha, _ => by
    intro ins h; simp only [code, List.mem_cons, List.mem_nil_iff, or_false] at h
    subst h; simp only [jmp, Instr.Valid]; omega
  | .reject, s, acc, rej, m, _, _, _, hr => by
    intro ins h; simp only [code, List.mem_cons, List.mem_nil_iff, or_false] at h
    subst h; simp only [jmp, Instr.Valid]; omega

/-- **Validity of the lowering**: `low(S)` is valid for `r = J + 7` registers. -/
theorem lower_valid (P : Program) (hP : P.WF) : (lower P).Valid P.regCount := by
  have hlen := lower_length P
  refine ⟨by omega, ?_, fun i hi => ?_⟩
  · have : (lower P).length - 1 = P.body.len + 1 + P.regCount := by omega
    simp only [this, lower, List.append_assoc]
    rw [List.getElem_append_right (by simp [code_length])]
    simp [code_length, cleanup]
  · suffices h : (lower P)[i].Valid P.regCount (P.body.len + P.regCount + 2) by rwa [← hlen] at h
    by_cases h1 : i < P.body.len
    · have : (lower P)[i] = (code P.bound P.body 0 (P.body.len + 1) P.body.len)[i]'(by
          rw [code_length]; exact h1) := by
        simp only [lower, List.append_assoc]; rw [List.getElem_append_left]
      rw [this]
      exact code_valid P.body hP.regs (by simp; omega) (by omega) (by omega) _ (List.getElem_mem _)
    · by_cases h2 : i = P.body.len
      · subst h2
        have : (lower P)[P.body.len] = jmp P.bound P.body.len := by
          simp only [lower, List.append_assoc]
          rw [List.getElem_append_right (by simp [code_length])]
          simp [code_length]
        rw [this]; simp only [jmp, Instr.Valid, Program.regCount]; omega
      · have hi' : i - (P.body.len + 1) < P.regCount := by omega
        have : (lower P)[i] = .dec (i - (P.body.len + 1)) (P.body.len + 1 + (i - (P.body.len + 1)))
            (P.body.len + 1 + (i - (P.body.len + 1)) + 1) := by
          simp only [lower, List.append_assoc, List.getElem_append, code_length, cleanup,
            List.length_cons, List.length_nil, List.length_map, List.length_range]
          simp only [h1, ite_false]
          have e : i - P.body.len = (i - (P.body.len + 1)) + 1 := by omega
          simp only [e, List.getElem_cons_succ, List.getElem_singleton]
          have h3 : ¬ (i - (P.body.len + 1) + 1 < 0 + 1) := by omega
          have h4 : i - (P.body.len + 1) + 1 - (0 + 1) < P.regCount := by omega
          simp only [dite_false, h3, h4, dite_true, List.getElem_map, List.getElem_range]
          simp
        rw [this]; simp only [Instr.Valid]; omega

end ZInQ.Compiler.IR
