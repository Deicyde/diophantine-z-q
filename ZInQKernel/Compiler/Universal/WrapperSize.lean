import ZInQKernel.Compiler.Programs
import ZInQKernel.Compiler.Universal.CodeSize

/-!
# Size of the wrapper

The wrapper `𝒲` has `m_𝒲` instructions with `3 ≤ m_𝒲 ≤ 200,000`, and every register index and
every target of its instructions is below `2^18` (`wrapper_small`).

The wrapper is never evaluated as a list. The lowering is bounded structurally: every field of
the open code `code J S s acc rej` is at most `max (J + 6, regs(S), s + |S|, acc, rej)`, where
`regs(S)` is the largest register of `S` (`code_fields_le`); hence every field of `low(P)` is at
most `max (J + 6, regs(S), |S| + J + 8)` and every field of the wrapper at most
`|Π| + max (…)` of the precision machine, or a field of the prefix `Π`. The finite inputs are
the lengths and largest registers of the two ideal programs, evaluated by the kernel on the
ideal syntax (`decide +kernel`).

(Blueprint: `compiler/natural/universal/wrapper-size-check.md`.)
-/

namespace ZInQ.Compiler.Universal

open RM IR

/-- The largest register of a right-hand side (`0` if none). -/
def opMaxReg : Op → ℕ
  | .const _ => 0
  | .copy y => y
  | .add y z | .sub y z | .mul y z | .div y z | .mod y z => max y z

/-- The largest register of a statement (`0` if none). -/
def stmtMaxReg : Stmt → ℕ
  | .assign x o => max x (opMaxReg o)
  | .seq s t => max (stmtMaxReg s) (stmtMaxReg t)
  | .ifLt y z s t | .ifEq y z s t => max (max y z) (max (stmtMaxReg s) (stmtMaxReg t))
  | .whileLt y z s => max (max y z) (stmtMaxReg s)
  | .accept | .reject => 0

/-- The instruction is not a halt, its register index is at most `R` and its targets at most
`T`. -/
def InstrLe (R T : ℕ) : Instr → Prop
  | .inc j x => j ≤ R ∧ x ≤ T
  | .dec j x y => j ≤ R ∧ x ≤ T ∧ y ≤ T
  | .halt => False

/-- Every instruction of `l` has register index at most `R` and targets at most `T`. -/
def BlockLe (l : List Instr) (R T : ℕ) : Prop := ∀ ins ∈ l, InstrLe R T ins

theorem InstrLe.mono {R T R' T' : ℕ} {ins : Instr} (h : InstrLe R T ins) (hR : R ≤ R')
    (hT : T ≤ T') : InstrLe R' T' ins := by
  cases ins <;> simp only [InstrLe] at h ⊢ <;> omega

theorem InstrLe.maxField {R T : ℕ} {ins : Instr} (h : InstrLe R T ins) :
    instrMaxField ins ≤ max R T := by
  cases ins <;> simp only [InstrLe, instrMaxField] at h ⊢ <;> omega

theorem InstrLe.valid {R T r m : ℕ} {ins : Instr} (h : InstrLe R T ins) (hR : R < r)
    (hT : T < m) : ins.Valid r m := by
  cases ins <;> simp only [InstrLe, Instr.Valid] at h ⊢ <;> omega

theorem BlockLe.append {l l' : List Instr} {R T : ℕ} (h : BlockLe l R T) (h' : BlockLe l' R T) :
    BlockLe (l ++ l') R T := fun ins hins => by
  rcases List.mem_append.1 hins with h1 | h1
  · exact h ins h1
  · exact h' ins h1

theorem BlockLe.mono {l : List Instr} {R T R' T' : ℕ} (h : BlockLe l R T) (hR : R ≤ R')
    (hT : T ≤ T') : BlockLe l R' T' := fun ins hins => (h ins hins).mono hR hT

set_option hygiene false in
/-- Proves `BlockLe` of an explicit block of the lowering. -/
macro "block_tac" : tactic => `(tactic| (
  simp only [BlockLe, assignB, divModB, ltTest, eqTest, snap2, snap, transfer1, transfer2,
    clearB, jmp, aux, List.cons_append, List.nil_append, List.forall_mem_cons, InstrLe,
    List.length_cons, List.length_nil, Bool.false_eq_true, ↓reduceIte, List.not_mem_nil,
    IsEmpty.forall_iff, implies_true, and_true, opMaxReg, Op.len, List.singleton_append]
  all_goals omega))

theorem divModB_le (J x y z : ℕ) (isDiv : Bool) (s : ℕ) :
    BlockLe (divModB J x y z isDiv s) (max (J + 6) (max x (max y z)))
      (s + if isDiv then 48 else 50) := by
  cases isDiv <;> block_tac

theorem incs_le (x k s : ℕ) : BlockLe (incs x k s) x (s + k + 1) := by
  intro ins hins
  simp only [incs, List.mem_map, List.mem_range] at hins
  obtain ⟨i, hi, rfl⟩ := hins
  simp only [InstrLe]
  omega

theorem assignB_le (J x : ℕ) (o : Op) (s : ℕ) :
    BlockLe (assignB J x o s) (max (J + 6) (max x (opMaxReg o))) (s + o.len) := by
  cases o with
  | const k =>
    refine BlockLe.append ?_ ((incs_le x k s).mono (by omega) (by simp only [Op.len]; omega))
    block_tac
  | div y z =>
    exact (divModB_le J x y z true s).mono (by simp [opMaxReg]) (by simp [Op.len])
  | mod y z =>
    exact (divModB_le J x y z false s).mono (by simp [opMaxReg]) (by simp [Op.len])
  | _ => block_tac

theorem ltTest_le (J y z s th el : ℕ) :
    BlockLe (ltTest J y z s th el) (max (J + 6) (max y z)) (max (s + 20) (max th el)) := by
  block_tac

theorem eqTest_le (J y z s th el : ℕ) :
    BlockLe (eqTest J y z s th el) (max (J + 6) (max y z)) (max (s + 22) (max th el)) := by
  block_tac

theorem jmp_le (J x : ℕ) {R T : ℕ} (hJ : J ≤ R) (hx : x ≤ T) : BlockLe [jmp J x] R T := by
  simp only [BlockLe, jmp, List.forall_mem_cons, InstrLe, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  omega

/-- **Fields of the open code**: registers at most `max (J + 6, regs(S))`, targets at most
`max (s + |S|, acc, rej)`. -/
theorem code_le (J : ℕ) (S : Stmt) (s acc rej : ℕ) :
    BlockLe (IR.code J S s acc rej) (max (J + 6) (stmtMaxReg S))
      (max (s + S.len) (max acc rej)) := by
  induction S generalizing s with
  | assign x o =>
    exact (assignB_le J x o s).mono (by simp only [stmtMaxReg]; omega)
      (by simp only [Stmt.len]; omega)
  | seq S T ihS ihT =>
    simp only [IR.code]
    exact ((ihS s).mono (by simp only [stmtMaxReg]; omega) (by simp only [Stmt.len]; omega)).append
      ((ihT _).mono (by simp only [stmtMaxReg]; omega) (by simp only [Stmt.len]; omega))
  | ifLt y z S T ihS ihT =>
    simp only [IR.code]
    refine ((((ltTest_le J y z s _ _).mono ?_ ?_).append ((ihS _).mono ?_ ?_)).append
      (jmp_le J _ ?_ ?_)).append ((ihT _).mono ?_ ?_)
    all_goals simp only [stmtMaxReg, Stmt.len]; omega
  | ifEq y z S T ihS ihT =>
    simp only [IR.code]
    refine ((((eqTest_le J y z s _ _).mono ?_ ?_).append ((ihS _).mono ?_ ?_)).append
      (jmp_le J _ ?_ ?_)).append ((ihT _).mono ?_ ?_)
    all_goals simp only [stmtMaxReg, Stmt.len]; omega
  | whileLt y z S ih =>
    simp only [IR.code]
    refine (((ltTest_le J y z s _ _).mono ?_ ?_).append ((ih _).mono ?_ ?_)).append
      (jmp_le J _ ?_ ?_)
    all_goals simp only [stmtMaxReg, Stmt.len]; omega
  | accept => exact jmp_le J _ (by omega) (by omega)
  | reject => exact jmp_le J _ (by omega) (by omega)

/-- The lowering without its final halt. -/
def lowerBody (P : IR.Program) : List Instr :=
  IR.code P.bound P.body 0 (P.body.len + 1) P.body.len ++ [jmp P.bound P.body.len] ++
    cleanup P.regCount (P.body.len + 1)

theorem lower_eq (P : IR.Program) : lower P = lowerBody P ++ [.halt] := rfl

theorem lowerBody_length (P : IR.Program) :
    (lowerBody P).length = P.body.len + P.bound + 8 := by
  simp only [lowerBody, List.length_append, code_length, List.length_singleton, cleanup,
    List.length_map, List.length_range, Program.regCount]
  omega

/-- **Fields of the lowering** `low(P)` before its final halt: no halt, registers at most
`max (J + 6, regs(S))`, targets at most `|S| + J + 8`. -/
theorem lowerBody_le (P : IR.Program) :
    BlockLe (lowerBody P) (max (P.bound + 6) (stmtMaxReg P.body)) (P.body.len + P.bound + 8) := by
  unfold lowerBody
  refine (((code_le P.bound P.body 0 (P.body.len + 1) P.body.len).mono le_rfl
    (by omega)).append (jmp_le _ _ (by omega) (by omega))).append ?_
  intro ins hins
  simp only [cleanup, Program.regCount, List.mem_map, List.mem_range] at hins
  obtain ⟨i, hi, rfl⟩ := hins
  simp only [InstrLe]
  omega

theorem relocate_le {R T d : ℕ} {ins : Instr} (h : InstrLe R T ins) :
    InstrLe R (d + T) (relocate d ins) := by
  cases ins <;> simp only [relocate, InstrLe] at h ⊢ <;> omega

/-! ### The wrapper -/

/-- The register bound of `Π ‖ low(P)`, for the open code `Π` of `U`. -/
def prefixedRegs (U P : IR.Program) : ℕ :=
  max (max (U.bound + 6) (stmtMaxReg U.body)) (max (P.bound + 6) (stmtMaxReg P.body))

/-- The program `Π ‖ (low(P) relocated by |Π|)`, for the open code `Π` of `U` at `0`. -/
def prefixed (U P : IR.Program) : RM.Program :=
  IR.code U.bound U.body 0 0 0 ++ (lower P).map (relocate (IR.code U.bound U.body 0 0 0).length)

theorem prefixed_eq (U P : IR.Program) :
    prefixed U P = (IR.code U.bound U.body 0 0 0 ++
      (lowerBody P).map (relocate U.body.len)) ++ [.halt] := by
  simp [prefixed, lower_eq, code_length, relocate]

theorem prefixed_length (U P : IR.Program) :
    (prefixed U P).length = U.body.len + (P.body.len + P.bound + 9) := by
  rw [prefixed_eq]
  simp only [List.length_append, List.length_map, code_length, lowerBody_length,
    List.length_singleton]
  omega

/-- Before the final halt, `Π ‖ low(P)` has no halt, registers at most `prefixedRegs U P` and
targets below its length. -/
theorem prefixed_body_le (U P : IR.Program) :
    BlockLe (IR.code U.bound U.body 0 0 0 ++ (lowerBody P).map (relocate U.body.len))
      (prefixedRegs U P) (U.body.len + (P.body.len + P.bound + 8)) := by
  refine ((code_le _ _ _ _ _).mono ?_ ?_).append ?_
  · simp only [prefixedRegs]; omega
  · omega
  · intro ins hins
    obtain ⟨ins', h', rfl⟩ := List.mem_map.1 hins
    exact (relocate_le (lowerBody_le P ins' h')).mono (by simp only [prefixedRegs]; omega) le_rfl

/-- **`Π ‖ low(P)` is valid** for every register count above its registers. -/
theorem prefixed_valid (U P : IR.Program) {r : ℕ} (hr : prefixedRegs U P < r) :
    (prefixed U P).Valid r := by
  have hl := prefixed_length U P
  have hb := prefixed_body_le U P
  have he := prefixed_eq U P
  generalize IR.code U.bound U.body 0 0 0 ++ (lowerBody P).map (relocate U.body.len) = A at hb he
  have hA : (prefixed U P).length = A.length + 1 := by rw [he, List.length_append]; rfl
  refine ⟨by omega, ?_, fun i hi => ?_⟩
  · simp only [he]
    simp
  · have hiA : i < A.length := by omega
    have : (prefixed U P)[i] = A[i] := by
      simp only [he]
      exact List.getElem_append_left hiA
    rw [this]
    exact (hb _ (List.getElem_mem hiA)).valid hr (by omega)

/-- Every field of `Π ‖ low(P)` is at most `max (prefixedRegs U P, |S_U| + |S_P| + J_P + 8)`. -/
theorem prefixed_fields (U P : IR.Program) (ins : Instr) (hins : ins ∈ prefixed U P) :
    instrMaxField ins ≤ max (prefixedRegs U P) (U.body.len + (P.body.len + P.bound + 8)) := by
  rw [prefixed_eq] at hins
  rcases List.mem_append.1 hins with h | h
  · exact (prefixed_body_le U P ins h).maxField
  · rw [List.mem_singleton.1 h]; simp [instrMaxField]

theorem wrapper_eq : wrapper = prefixed unpairProgram precisionProgram := rfl

theorem wrapper_length : wrapper.length =
    unpairProgram.body.len + (precisionProgram.body.len + precisionProgram.bound + 9) := by
  rw [wrapper_eq, prefixed_length]

/-- The finite inputs of the size check: the lengths and largest registers of the unpairing
program and of the precision program, evaluated by the kernel on the ideal syntax. -/
theorem wrapper_numbers :
    max (prefixedRegs unpairProgram precisionProgram)
        (unpairProgram.body.len + (precisionProgram.body.len + precisionProgram.bound + 8)) <
      2 ^ 18 ∧
    unpairProgram.body.len + (precisionProgram.body.len + precisionProgram.bound + 9) ≤ 200000 := by
  decide +kernel

/-- **Size of the wrapper**: `3 ≤ m_𝒲 ≤ 200,000`, and every register index and target of the
wrapper is below `2^18`. -/
theorem wrapper_small : SmallProgram wrapper := by
  obtain ⟨h1, h2⟩ := wrapper_numbers
  refine ⟨?_, ?_, fun ins hins => ?_⟩
  · rw [wrapper_length]; omega
  · rw [wrapper_length]; exact h2
  · rw [wrapper_eq] at hins
    exact (prefixed_fields _ _ ins hins).trans_lt h1

/-- **The wrapper is valid** for `2^18` registers. -/
theorem wrapper_valid : wrapper.Valid (2 ^ 18) := by
  rw [wrapper_eq]
  exact prefixed_valid _ _ (lt_of_le_of_lt (le_max_left _ _) wrapper_numbers.1)

end ZInQ.Compiler.Universal
