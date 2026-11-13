import ZInQKernel.Compiler.Circuits.RegisterMachine

/-!
# The universal program numbering

Every `e : ℕ` is uniquely `e + 1 = 2 ^ w * (2 * D + 1)`. The machine `μ_e` numbered by `e`
halts at once if `w = 0`; otherwise state `i` reads the four base-`2 ^ w` digits
`(o, j, x, y)` of `D` at positions `4i, …, 4i + 3` and is `inc j x` if `o = 1`,
`dec j x y` if `o = 2` and `halt` otherwise. The program numbered `e` halts on `n` if the
run of `μ_e` from state `0` with `n` in register `0` reaches a halt instruction.

The code of a primitive program `p` uses the least width `w(p) ≥ 2` bounding all fields and
the base-`2 ^ w(p)` number `D(p)` whose digits are the four fields of each instruction.

(Blueprint: `compiler/natural/universal/program-numbering.md`.)
-/

namespace ZInQ.Compiler.Universal

open RM

/-! ### Decoding -/

/-- The decomposition `e + 1 = 2 ^ w * (2 * D + 1)`: `split2 e = (w, D)`. -/
def split2 (e : ℕ) : ℕ × ℕ :=
  (padicValNat 2 (e + 1), ((e + 1) / 2 ^ padicValNat 2 (e + 1)) / 2)

/-- The `t`-th base-`2 ^ w` digit of `D`. -/
def digit (w D t : ℕ) : ℕ := D / 2 ^ (w * t) % 2 ^ w

/-- The instruction read from the four digits `(o, j, x, y)`. -/
def decodeInstr (o j x y : ℕ) : Instr :=
  if o = 1 then .inc j x else if o = 2 then .dec j x y else .halt

/-- The machine numbered `e`. -/
def decodeMachine (e : ℕ) : Machine := fun i =>
  if (split2 e).1 = 0 then .halt else
    decodeInstr (digit (split2 e).1 (split2 e).2 (4 * i))
      (digit (split2 e).1 (split2 e).2 (4 * i + 1))
      (digit (split2 e).1 (split2 e).2 (4 * i + 2))
      (digit (split2 e).1 (split2 e).2 (4 * i + 3))

/-- The program numbered `e` halts on input `n`: the run of `μ_e` from state `0`, with `n` in
register `0` and all other registers zero, reaches a halt instruction. -/
def halts (e n : ℕ) : Prop := RM.Halts (decodeMachine e) (initFile ![n])

/-- Uniqueness of the decomposition. -/
theorem split2_eq_of {e w D : ℕ} (h : e + 1 = 2 ^ w * (2 * D + 1)) : split2 e = (w, D) := by
  have hv : padicValNat 2 (e + 1) = w := by
    rw [h, padicValNat.mul (by positivity) (by omega), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by omega), add_zero]
  unfold split2
  rw [hv, h, Nat.mul_div_cancel_left _ (by positivity)]
  congr 1
  omega

theorem split2_spec (e : ℕ) : e + 1 = 2 ^ (split2 e).1 * (2 * (split2 e).2 + 1) := by
  obtain ⟨w, m, hm, he⟩ := Nat.exists_eq_two_pow_mul_odd (n := e + 1) (by omega)
  obtain ⟨D, rfl⟩ := hm
  rw [split2_eq_of (show e + 1 = 2 ^ w * (2 * D + 1) by rw [he])]
  exact he

theorem decodeMachine_of_w_eq_zero {e : ℕ} (h : (split2 e).1 = 0) (i : ℕ) :
    decodeMachine e i = .halt := by
  simp [decodeMachine, h]

theorem decodeMachine_of_w_ne_zero {e : ℕ} (h : (split2 e).1 ≠ 0) (i : ℕ) :
    decodeMachine e i = decodeInstr (digit (split2 e).1 (split2 e).2 (4 * i))
      (digit (split2 e).1 (split2 e).2 (4 * i + 1))
      (digit (split2 e).1 (split2 e).2 (4 * i + 2))
      (digit (split2 e).1 (split2 e).2 (4 * i + 3)) := by
  simp [decodeMachine, h]

/-! ### Encoding -/

/-- The four fields of an instruction: `(1, j, x, 0)`, `(2, j, x, y)`, `(0, 0, 0, 0)`. -/
def instrFields : Instr → List ℕ
  | .inc j x => [1, j, x, 0]
  | .dec j x y => [2, j, x, y]
  | .halt => [0, 0, 0, 0]

/-- The largest register index or target of an instruction. -/
def instrMaxField : Instr → ℕ
  | .inc j x => max j x
  | .dec j x y => max j (max x y)
  | .halt => 0

/-- The largest register index or target of a program. -/
def maxField (p : Program) : ℕ := (p.map instrMaxField).foldr max 0

/-- The width `w(p)`: the least `w ≥ 2` such that every register index and target of `p` is
below `2 ^ w`. -/
def width (p : Program) : ℕ := max 2 (Nat.size (maxField p))

/-- The field digits of `p`, instruction by instruction. -/
def fieldsOf (p : Program) : List ℕ := p.flatMap instrFields

/-- `D(p) = ∑_{i<m} ∑_{t<4} f_{i,t} 2^{w(p)(4i+t)}`, as a base-`2^w(p)` number. -/
def codeD (p : Program) : ℕ := Nat.ofDigits (2 ^ width p) (fieldsOf p)

/-- `code(p) = 2^{w(p)} (2 D(p) + 1) - 1`. -/
def code (p : Program) : ℕ := 2 ^ width p * (2 * codeD p + 1) - 1

/-- The least-width characterization of `width`. -/
theorem width_spec (p : Program) :
    2 ≤ width p ∧ maxField p < 2 ^ width p ∧
      ∀ w, 2 ≤ w → maxField p < 2 ^ w → width p ≤ w := by
  refine ⟨le_max_left _ _, ?_, fun w hw h => max_le hw (Nat.size_le.mpr h)⟩
  exact lt_of_lt_of_le (Nat.lt_size_self _) (Nat.pow_le_pow_right (by norm_num) (le_max_right _ _))

theorem fieldsOf_length (p : Program) : (fieldsOf p).length = 4 * p.length := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [fieldsOf, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    rw [ih]
    cases a <;> simp [instrFields] <;> ring

/-- `D(p)` as the double sum of the article. -/
theorem codeD_eq_sum (p : Program) :
    codeD p = ∑ i ∈ Finset.range p.length, ∑ t ∈ Finset.range 4,
      (instrFields (p.getD i .halt)).getD t 0 * 2 ^ (width p * (4 * i + t)) := by
  have key : ∀ (q : Program) (b : ℕ), Nat.ofDigits b (fieldsOf q) =
      ∑ i ∈ Finset.range q.length, ∑ t ∈ Finset.range 4,
        (instrFields (q.getD i .halt)).getD t 0 * b ^ (4 * i + t) := by
    intro q b
    induction q with
    | nil => simp [fieldsOf]
    | cons a q ih =>
      have hlen : (instrFields a).length = 4 := by cases a <;> rfl
      simp only [fieldsOf, List.flatMap_cons] at ih ⊢
      rw [Nat.ofDigits_append, ih, hlen, List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
      simp only [List.getD_cons_succ, List.getD_cons_zero, Finset.mul_sum]
      rw [add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => ?_
        ring
      · cases a <;> simp [instrFields, Finset.sum_range_succ, Nat.ofDigits] <;> ring
  rw [codeD, key]
  simp only [← pow_mul]

end ZInQ.Compiler.Universal
