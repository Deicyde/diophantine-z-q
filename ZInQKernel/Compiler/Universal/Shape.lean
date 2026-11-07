import ZInQKernel.Compiler.Universal.Interpreter

/-!
# Shape of the universal interpreter

The universal interpreter `𝒰` satisfies the following closed decidable statements:

1. it is valid for `204` registers, has `m = 1,399` instructions, and its final instruction
   (state `1398`) is the halt;
2. it has `s = 1,022` sub instructions and `376` add instructions;
3. its cleanup stage: for `j < 204` the instruction at state `1194 + j` is
   `dec(j, 1194 + j, 1195 + j)`;
4. the states below `1194` having a target at least `1194` are exactly `69`, `587` and `593`,
   and each of them is `dec(2, 1194, 1194)`.

Each is a kernel computation on the literal program, through a Boolean checker or a list
equality evaluated by `decide +kernel` (linear passes over the list, no indexed access in a
loop), with a soundness lemma where the statement is not itself decidable.

(Blueprint: `compiler/natural/universal/interpreter-shape.md`.)
-/

namespace ZInQ.Compiler.Universal

open RM

/-- The targets of an instruction. -/
def instrTargets : Instr → List ℕ
  | .inc _ x => [x]
  | .dec _ x y => [x, y]
  | .halt => []

/-- Boolean form of `Instr.Valid r m`. -/
def instrValidB (r m : ℕ) : Instr → Bool
  | .inc j x => decide (j < r) && decide (x < m)
  | .dec j x y => decide (j < r) && decide (x < m) && decide (y < m)
  | .halt => false

theorem instrValidB_sound {r m : ℕ} {ins : Instr} (h : instrValidB r m ins = true) :
    ins.Valid r m := by
  cases ins <;> simp_all [instrValidB, Instr.Valid]

/-- With `ins` the current instruction and `rest` the following ones: every instruction but the
last passes `instrValidB r m`, and the last one is the halt. -/
def validTail (r m : ℕ) : Instr → Program → Bool
  | ins, [] => decide (ins = .halt)
  | ins, next :: rest => instrValidB r m ins && validTail r m next rest

theorem validTail_sound {r m : ℕ} : ∀ {ins : Instr} {rest : Program},
    validTail r m ins rest = true →
      (ins :: rest)[rest.length] = .halt ∧
        ∀ i (hi : i + 1 < (ins :: rest).length), (ins :: rest)[i].Valid r m
  | ins, [], h => by
    simp only [validTail, decide_eq_true_eq] at h
    exact ⟨by simpa using h, fun i hi => by simp at hi⟩
  | ins, next :: rest, h => by
    simp only [validTail, Bool.and_eq_true] at h
    obtain ⟨hlast, hall⟩ := validTail_sound h.2
    refine ⟨by simpa using hlast, fun i hi => ?_⟩
    rcases i with _ | i
    · exact instrValidB_sound h.1
    · exact hall i (by simpa using hi)

/-- Boolean validity check for `r` registers. -/
def programValidB (p : Program) (r : ℕ) : Bool :=
  match p with
  | [] => false
  | ins :: rest => validTail r (rest.length + 1) ins rest

theorem programValidB_sound {p : Program} {r : ℕ} (h : programValidB p r = true) :
    p.Valid r := by
  match p, h with
  | ins :: rest, h =>
    obtain ⟨hlast, hall⟩ := validTail_sound h
    exact ⟨by simp, by simpa using hlast, hall⟩

/-! ### The kernel computations -/

theorem interpreter_validB : programValidB interpreter 204 = true := by decide +kernel

theorem interpreter_length : interpreter.length = 1399 := by decide +kernel

theorem interpreter_subCount : interpreter.subCount = 1022 := by decide +kernel

theorem interpreter_addCount : interpreter.addCount = 376 := by decide +kernel

/-- The cleanup stage and the final halt, as a list equality. -/
theorem interpreter_drop_cleanup :
    interpreter.drop 1194 =
      (List.range 204).map (fun j => Instr.dec j (1194 + j) (1195 + j)) ++ [.halt] := by
  decide +kernel

/-- The states below `1194` with a target at least `1194`, with their instructions. -/
theorem interpreter_cleanup_entries :
    (interpreter.take 1194).zipIdx.filter (fun e => (instrTargets e.1).any (1194 ≤ ·)) =
      [(.dec 2 1194 1194, 69), (.dec 2 1194 1194, 587), (.dec 2 1194 1194, 593)] := by
  decide +kernel

/-! ### The shape statement -/

theorem interpreter_valid : interpreter.Valid 204 := programValidB_sound interpreter_validB

theorem interpreter_getElem?_cleanup {j : ℕ} (hj : j < 204) :
    interpreter[1194 + j]? = some (.dec j (1194 + j) (1195 + j)) := by
  have h := congrArg (·[j]?) interpreter_drop_cleanup
  simp only [List.getElem?_drop] at h
  rw [h, List.getElem?_append_left (by simpa using hj)]
  simp [hj]

theorem interpreter_getElem?_last : interpreter[1398]? = some .halt := by
  have h := congrArg (·[204]?) interpreter_drop_cleanup
  simpa using h

theorem interpreter_getElem?_entry {i : ℕ} (hi : i = 69 ∨ i = 587 ∨ i = 593) :
    interpreter[i]? = some (.dec 2 1194 1194) := by
  have hmem : ((Instr.dec 2 1194 1194 : Instr), i) ∈
      (interpreter.take 1194).zipIdx.filter (fun e => (instrTargets e.1).any (1194 ≤ ·)) := by
    rw [interpreter_cleanup_entries]
    rcases hi with rfl | rfl | rfl <;> simp
  have h := (List.mem_zipIdx_iff_getElem?.1 (List.mem_filter.1 hmem).1)
  rw [List.getElem?_take] at h
  split_ifs at h
  exact h

theorem interpreter_entry_iff {i : ℕ} {ins : Instr} (hi : i < 1194)
    (hins : interpreter[i]? = some ins) :
    (∃ t ∈ instrTargets ins, 1194 ≤ t) ↔ i = 69 ∨ i = 587 ∨ i = 593 := by
  constructor
  · rintro ⟨t, ht, hle⟩
    have hmem : (ins, i) ∈
        (interpreter.take 1194).zipIdx.filter (fun e => (instrTargets e.1).any (1194 ≤ ·)) := by
      refine List.mem_filter.2 ⟨List.mem_zipIdx_iff_getElem?.2 ?_, ?_⟩
      · simpa [List.getElem?_take, hi] using hins
      · simpa using ⟨t, ht, hle⟩
    rw [interpreter_cleanup_entries] at hmem
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    omega
  · intro h
    rw [interpreter_getElem?_entry h] at hins
    cases hins
    exact ⟨1194, by simp [instrTargets], le_rfl⟩

/-- **Shape of the universal interpreter.** -/
theorem interpreter_shape :
    interpreter.Valid 204 ∧ interpreter.length = 1399 ∧ interpreter[1398]? = some .halt ∧
    interpreter.subCount = 1022 ∧ interpreter.addCount = 376 ∧
    (∀ j < 204, interpreter[1194 + j]? = some (.dec j (1194 + j) (1195 + j))) ∧
    (∀ i < 1194, ∀ ins, interpreter[i]? = some ins →
      ((∃ t ∈ instrTargets ins, 1194 ≤ t) ↔ i = 69 ∨ i = 587 ∨ i = 593)) ∧
    (∀ i, i = 69 ∨ i = 587 ∨ i = 593 → interpreter[i]? = some (.dec 2 1194 1194)) :=
  ⟨interpreter_valid, interpreter_length, interpreter_getElem?_last, interpreter_subCount,
    interpreter_addCount, fun _ hj => interpreter_getElem?_cleanup hj,
    fun _ hi _ hins => interpreter_entry_iff hi hins, fun _ hi => interpreter_getElem?_entry hi⟩

end ZInQ.Compiler.Universal
