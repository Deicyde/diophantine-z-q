import ZInQKernel.Compiler.Programs.WrapperCorrect
import ZInQKernel.Compiler.Programs.LoweringValid

/-!
# Validity of the precision machine and of the wrapper

Blueprint: `compiler/natural/programs/precision-machine.md` and `wrapper-program.md`.

`M_prec` is valid for `r_prec` registers, and the wrapper `𝒲` is valid for `r_prec + 10`
registers (the prefix uses the registers `0, …, 4` and `r_prec, …, r_prec + 9`).
-/

namespace ZInQ.Compiler.IR

open RM

theorem precisionMachine_valid : precisionMachine.Valid precRegs :=
  lower_valid precisionProgram precisionProgram_wf

theorem Instr.Valid.mono {r r' m m' : ℕ} {ins : Instr} (h : ins.Valid r m) (hr : r ≤ r')
    (hm : m ≤ m') : ins.Valid r' m' := by
  cases ins <;> simp only [Instr.Valid] at h ⊢ <;> omega

theorem relocate_valid {r m d : ℕ} {ins : Instr} (h : ins.Valid r m) :
    (relocate d ins).Valid r (d + m) := by
  cases ins <;> simp only [relocate, Instr.Valid] at h ⊢ <;> omega

/-- A prefix followed by a relocated valid program is valid. -/
theorem append_relocate_valid {Pf M : List Instr} {R r : ℕ} (hM : RM.Program.Valid M r)
    (hr : r ≤ R) (hPf : ∀ ins ∈ Pf, ins.Valid R (Pf.length + M.length)) :
    RM.Program.Valid (Pf ++ M.map (relocate Pf.length)) R := by
  have hpos := hM.pos
  have hl : (Pf ++ M.map (relocate Pf.length)).length = Pf.length + M.length := by simp
  refine ⟨by omega, ?_, fun i hi => ?_⟩
  · have hlast := hM.last
    have hi1 : Pf.length ≤ (Pf ++ M.map (relocate Pf.length)).length - 1 := by omega
    rw [List.getElem_append_right hi1, List.getElem_map]
    have e : (Pf ++ M.map (relocate Pf.length)).length - 1 - Pf.length = M.length - 1 := by omega
    simp only [e, hlast]; rfl
  · suffices h : (Pf ++ M.map (relocate Pf.length))[i].Valid R (Pf.length + M.length) by
      rwa [← hl] at h
    by_cases hd : i < Pf.length
    · rw [List.getElem_append_left hd]
      exact hPf _ (List.getElem_mem hd)
    · rw [List.getElem_append_right (by omega), List.getElem_map]
      have hj : i - Pf.length + 1 < M.length := by omega
      exact Instr.Valid.mono (relocate_valid (d := Pf.length) (hM.valid _ hj)) hr le_rfl

theorem wrapper_eq : wrapper = wrapperPrefix ++ precisionMachine.map (relocate wrapperPrefix.length) :=
  rfl

/-- **Validity of the wrapper** for `r_prec + 10` registers. -/
theorem wrapper_valid : wrapper.Valid (precRegs + 10) := by
  rw [wrapper_eq]
  refine append_relocate_valid (r := precRegs) precisionMachine_valid (by omega)
    (fun ins hins => ?_)
  have hpos := precisionMachine_pos
  have hwl : wrapperPrefix.length = unpairProgram.body.len := by rw [wrapperPrefix, code_length]
  simp only [wrapperPrefix] at hins
  have hc := code_valid (J := unpairProgram.bound) unpairProgram.body (s := 0) (acc := 0)
    (rej := 0) (m := wrapperPrefix.length + precisionMachine.length)
    (Stmt.regsBelow_of_regsBound unpairProgram_regsBound)
    (by rw [Nat.zero_add, ← hwl]; omega) (by omega) (by omega) ins hins
  exact Instr.Valid.mono hc (by simp only [unpairProgram]; omega) le_rfl

end ZInQ.Compiler.IR

namespace ZInQ.Compiler.IR

open RM

theorem wrapperPrefix_length_eq : wrapperPrefix.length = unpairProgram.body.len := by
  rw [wrapperPrefix, code_length]

/-- The length of the wrapper, as a structural count. -/
theorem wrapper_length_eq : wrapper.length =
    unpairProgram.body.len + (precisionProgram.body.len + precisionProgram.regCount + 2) := by
  rw [wrapper_length, wrapperPrefix_length_eq, precisionMachine, lower_length]

/-- **Size of the wrapper**: at most `200000` instructions, register indices below `2^18`, and
targets below the length (so below `2^18` as well). The counts are evaluated structurally by
the kernel on the syntax of the programs (`Stmt.len`), never on the instruction list. -/
theorem wrapper_size : 3 ≤ wrapper.length ∧ wrapper.length ≤ 200000 ∧ precRegs + 10 ≤ 2 ^ 18 := by
  rw [wrapper_length_eq]
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

end ZInQ.Compiler.IR
