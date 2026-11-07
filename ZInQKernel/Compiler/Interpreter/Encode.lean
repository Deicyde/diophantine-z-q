import ZInQKernel.Compiler.Interpreter.Numbering

/-!
# Codes of primitive programs

The machine numbered by `code p` is the machine of `p`: decoding recovers `w(p)` and `D(p)`,
and the base-`2 ^ w(p)` digits of `D(p)` are the fields of the instructions (zero beyond).
Hence `code p` halts on `n` exactly when `p` halts on the one input `n`. Moreover
`code p < 2 ^ (w(p) (4m + 1) + 1)`, and `code p + 1 ≥ 2 ^ (w(p) (4m - 7) + 1)` if `m ≥ 2`.

(Blueprint: `compiler/natural/universal/program-numbering-encode.md`.)
-/

namespace ZInQ.Compiler.Universal

open RM

/-! ### Base-`b` digits of `Nat.ofDigits` -/

/-- The `k`-th digit of `ofDigits b L` is the `k`-th entry of `L`, when every entry is below
`b`. -/
theorem ofDigits_div_pow_mod {b : ℕ} (hb : 0 < b) :
    ∀ (L : List ℕ), (∀ x ∈ L, x < b) → ∀ k, Nat.ofDigits b L / b ^ k % b = L.getD k 0
  | [], _, k => by simp [Nat.ofDigits]
  | a :: L, hL, 0 => by
    have ha : a < b := hL a (by simp)
    simp [Nat.ofDigits_cons, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
  | a :: L, hL, k + 1 => by
    have ha : a < b := hL a (by simp)
    have h : Nat.ofDigits b (a :: L) / b ^ (k + 1) = Nat.ofDigits b L / b ^ k := by
      rw [Nat.ofDigits_cons, pow_succ', ← Nat.div_div_eq_div_mul,
        Nat.add_mul_div_left _ _ hb, Nat.div_eq_of_lt ha, zero_add]
    rw [h, ofDigits_div_pow_mod hb L (fun x hx => hL x (by simp [hx])) k]
    simp

/-- Each digit contributes at most the whole number. -/
theorem getD_mul_pow_le_ofDigits (b : ℕ) :
    ∀ (L : List ℕ) (k : ℕ), L.getD k 0 * b ^ k ≤ Nat.ofDigits b L
  | [], k => by simp
  | a :: L, 0 => by simp [Nat.ofDigits_cons]
  | a :: L, k + 1 => by
    have := getD_mul_pow_le_ofDigits b L k
    simp only [List.getD_cons_succ, Nat.ofDigits_cons, pow_succ']
    nlinarith

/-! ### Fields -/

theorem instrFields_length (a : Instr) : (instrFields a).length = 4 := by cases a <;> rfl

theorem fieldsOf_getD (p : Program) (i t : ℕ) (ht : t < 4) :
    (fieldsOf p).getD (4 * i + t) 0 = (instrFields (p.getD i .halt)).getD t 0 := by
  induction p generalizing i with
  | nil =>
    simp only [fieldsOf, List.flatMap_nil, List.getD_eq_getElem?_getD,
      List.getElem?_nil, Option.getD_none]
    interval_cases t <;> rfl
  | cons a p ih =>
    simp only [fieldsOf, List.flatMap_cons] at ih ⊢
    rcases i with _ | i
    · rw [List.getD_append _ _ _ _ (by rw [instrFields_length]; omega)]
      simp
    · rw [List.getD_append_right _ _ _ _ (by rw [instrFields_length]; omega),
        instrFields_length, show 4 * (i + 1) + t - 4 = 4 * i + t by omega, ih]
      rfl

theorem le_maxField {p : Program} {a : Instr} (ha : a ∈ p) : instrMaxField a ≤ maxField p := by
  induction p with
  | nil => simp at ha
  | cons b p ih =>
    simp only [maxField, List.map_cons, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp ha with rfl | ha
    · exact le_max_left _ _
    · exact le_trans (ih ha) (le_max_right _ _)

theorem fieldsOf_lt (p : Program) : ∀ x ∈ fieldsOf p, x < 2 ^ width p := by
  intro x hx
  obtain ⟨a, ha, hx⟩ := List.mem_flatMap.mp hx
  have h1 := le_maxField ha
  obtain ⟨hw, hmax, -⟩ := width_spec p
  have h4 : 4 ≤ 2 ^ width p := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ width p := Nat.pow_le_pow_right (by norm_num) hw
  cases a <;> simp only [instrFields, instrMaxField, List.mem_cons, List.not_mem_nil,
    or_false] at hx h1 <;> rcases hx with rfl | rfl | rfl | rfl <;> omega

theorem decodeInstr_fields (a : Instr) :
    decodeInstr ((instrFields a).getD 0 0) ((instrFields a).getD 1 0) ((instrFields a).getD 2 0)
      ((instrFields a).getD 3 0) = a := by
  cases a <;> simp [instrFields, decodeInstr]

/-! ### Decoding a code -/

theorem width_pos (p : Program) : 0 < width p := by
  have := (width_spec p).1
  omega

theorem code_add_one (p : Program) : code p + 1 = 2 ^ width p * (2 * codeD p + 1) := by
  have : 0 < 2 ^ width p * (2 * codeD p + 1) := by positivity
  unfold code
  omega

theorem split2_code (p : Program) : split2 (code p) = (width p, codeD p) :=
  split2_eq_of (code_add_one p)

theorem digit_codeD (p : Program) (k : ℕ) :
    digit (width p) (codeD p) k = (fieldsOf p).getD k 0 := by
  rw [digit, pow_mul, codeD]
  exact ofDigits_div_pow_mod (by positivity) _ (fieldsOf_lt p) k

/-- The machine numbered by `code p` is the machine of `p`: `μ_{code p}(i) = p_i` for
`i < m` and `halt` for `i ≥ m`. -/
theorem decodeMachine_code (p : Program) : decodeMachine (code p) = p.toMachine := by
  funext i
  rw [decodeMachine_of_w_ne_zero (by rw [split2_code]; exact (width_pos p).ne'), split2_code]
  have h0 := fieldsOf_getD p i 0 (by norm_num)
  rw [add_zero] at h0
  simp only [digit_codeD]
  rw [h0, fieldsOf_getD p i 1 (by norm_num),
    fieldsOf_getD p i 2 (by norm_num), fieldsOf_getD p i 3 (by norm_num), decodeInstr_fields]
  rfl

/-- The pointwise form of `decodeMachine_code`. -/
theorem decodeMachine_code_of_lt (p : Program) {i : ℕ} (hi : i < p.length) :
    decodeMachine (code p) i = p[i] := by
  rw [decodeMachine_code, toMachine_of_lt p hi]

theorem decodeMachine_code_of_le (p : Program) {i : ℕ} (hi : p.length ≤ i) :
    decodeMachine (code p) i = .halt := by
  rw [decodeMachine_code, toMachine_of_le p hi]

/-! ### Halting -/

/-- A run of a valid program from a state below its length stays below its length. -/
theorem valid_step_state_lt {p : Program} {r : ℕ} (hp : p.Valid r) {c c' : Config}
    (hc : c.state < p.length) (h : step p.toMachine c = some c') : c'.state < p.length := by
  by_cases hlast : c.state = p.length - 1
  · have : p.toMachine c.state = .halt := (hp.toMachine_eq_halt_iff hc).mpr hlast
    rw [(step_eq_none_iff _ _).mpr this] at h
    cases h
  · have hv := hp.valid c.state (by omega)
    unfold step at h
    rw [toMachine_of_lt p hc] at h
    generalize p[c.state] = a at hv h
    cases a with
    | inc j x =>
      simp only [Option.some.injEq] at h
      subst h
      exact hv.2
    | dec j x y =>
      dsimp only at h
      split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h
      · exact hv.2.2
      · exact hv.2.1
    | halt => exact hv.elim

theorem valid_stepN_state_lt {p : Program} {r : ℕ} (hp : p.Valid r) :
    ∀ (t : ℕ) {c c' : Config}, c.state < p.length → stepN p.toMachine t c = some c' →
      c'.state < p.length
  | 0, c, c', hc, h => by cases h; exact hc
  | t + 1, c, c', hc, h => by
    rw [stepN_succ] at h
    cases hs : step p.toMachine c with
    | none => rw [hs] at h; cases h
    | some d =>
      rw [hs] at h
      exact valid_stepN_state_lt hp t (valid_step_state_lt hp hc hs) h

/-- `code p` halts on `n` exactly when the valid program `p` halts on the one input `n`. -/
theorem halts_code_iff (p : Program) (r : ℕ) (hp : p.Valid r) (n : ℕ) :
    halts (code p) n ↔ p.HaltsOn ![n] := by
  unfold halts RM.Halts Program.HaltsOn
  rw [decodeMachine_code]
  refine exists_congr fun t => exists_congr fun c => and_congr_right fun h => ?_
  exact hp.toMachine_eq_halt_iff (valid_stepN_state_lt hp t hp.pos h)

/-! ### Size bounds -/

theorem codeD_lt (p : Program) : codeD p < 2 ^ (width p * (4 * p.length)) := by
  rw [pow_mul, ← fieldsOf_length]
  exact Nat.ofDigits_lt_base_pow_length (Nat.one_lt_two_pow (width_pos p).ne') (fieldsOf_lt p)

/-- `code(p) < 2 ^ (w(p) (4m + 1) + 1)`. -/
theorem code_lt (p : Program) : code p < 2 ^ (width p * (4 * p.length + 1) + 1) := by
  have h1 := code_add_one p
  have h2 := codeD_lt p
  have : 2 ^ (width p * (4 * p.length + 1) + 1) =
      2 ^ width p * (2 * 2 ^ (width p * (4 * p.length))) := by
    rw [← pow_succ', ← pow_add]; congr 1; ring
  rw [this]
  have : 2 * codeD p + 1 < 2 * 2 ^ (width p * (4 * p.length)) := by omega
  have := Nat.mul_lt_mul_of_pos_left this (show 0 < 2 ^ width p by positivity)
  omega

/-- If `m ≥ 2`, then `code(p) + 1 ≥ 2 ^ (w(p) (4m - 7) + 1)`. -/
theorem code_ge (p : Program) (r : ℕ) (hp : p.Valid r) (hm : 2 ≤ p.length) :
    2 ^ (width p * (4 * p.length - 7) + 1) ≤ code p + 1 := by
  have hv := hp.valid (p.length - 2) (by omega)
  have hdig : 1 ≤ (fieldsOf p).getD (4 * (p.length - 2)) 0 := by
    have := fieldsOf_getD p (p.length - 2) 0 (by norm_num)
    rw [add_zero] at this
    rw [this, List.getD_eq_getElem?_getD (l := p), List.getElem?_eq_getElem (by omega),
      Option.getD_some]
    generalize p[p.length - 2] = a at hv
    cases a <;> simp_all [instrFields, Instr.Valid]
  have hD : 2 ^ (width p * (4 * (p.length - 2))) ≤ codeD p := by
    have := getD_mul_pow_le_ofDigits (2 ^ width p) (fieldsOf p) (4 * (p.length - 2))
    rw [← pow_mul] at this
    unfold codeD
    exact le_trans (Nat.le_mul_of_pos_left _ hdig) this
  rw [code_add_one]
  have : 2 ^ (width p * (4 * p.length - 7) + 1) =
      2 ^ width p * (2 * 2 ^ (width p * (4 * (p.length - 2)))) := by
    rw [← pow_succ', ← pow_add]; congr 1
    obtain ⟨k, hk⟩ : ∃ k, p.length = k + 2 := ⟨p.length - 2, by omega⟩
    rw [hk, show 4 * (k + 2) - 7 = 4 * k + 1 by omega, show k + 2 - 2 = k by omega]
    ring
  rw [this]
  exact Nat.mul_le_mul_left _ (by omega)

end ZInQ.Compiler.Universal
