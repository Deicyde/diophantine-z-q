import ZInQKernel.Compiler.Programs.PrecisionMachine
import ZInQKernel.Compiler.Programs.Cantor

/-!
# Correctness of the wrapper

Blueprint: `compiler/natural/programs/wrapper-correct.md`.

The prefix terminates (each decoder loop decreases its remainder) and reaches the first
relocated state with the initial file of `M_prec` on `dec₅(x)`; relocation by `|Π|` maps the
runs of `M_prec` onto the runs of the suffix of `𝒲`. Hence `𝒲` halts on `x` iff
`accepts(dec₅(x))`, and on `enc₅(c)` iff `accepts(c)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace ZInQ.Compiler.IR

open RM Precision CantorDecoder

/-- `dec₅(x)` as a tuple. -/
def dec5 (x : ℕ) : Fin 5 → ℕ :=
  ![(CantorDecoder.decode5 x).1, (CantorDecoder.decode5 x).2.1, (CantorDecoder.decode5 x).2.2.1,
    (CantorDecoder.decode5 x).2.2.2.1, (CantorDecoder.decode5 x).2.2.2.2]

theorem dec5_encode5 (c : Fin 5 → ℕ) : dec5 (encode5 (c 0) (c 1) (c 2) (c 3) (c 4)) = c := by
  funext i
  simp only [dec5, decode5_encode5]
  fin_cases i <;> rfl

/-! ### The prefix -/

theorem unpairLoop_spec (B : ℕ) : ∀ (r s : ℕ) (ρ : ℕ → ℕ), ρ B = s → ρ (B + 1) = r →
    ρ (B + 2) = 1 →
    ∃ ρ', BigStep (.whileLt B (B + 1) (asg B (.add B (B + 2)) ;; asg (B + 1) (.sub (B + 1) B))) ρ
      (.normal ρ') ∧ ρ' B - ρ' (B + 1) = (loop s r).1 ∧ ρ' (B + 1) = (loop s r).2 ∧
      ∀ v, v ≠ B → v ≠ B + 1 → ρ' v = ρ v := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro s ρ hs hr h1
    by_cases hc : s < r
    · set ρ₁ := Function.update (Function.update ρ B (ρ B + ρ (B + 2))) (B + 1)
        (Function.update ρ B (ρ B + ρ (B + 2)) (B + 1) - Function.update ρ B (ρ B + ρ (B + 2)) B)
        with hρ₁
      have e0 : ρ₁ B = s + 1 := by simp [hρ₁, hs, h1]
      have e1 : ρ₁ (B + 1) = r - (s + 1) := by simp [hρ₁, hs, h1, hr]
      have e2 : ρ₁ (B + 2) = 1 := by simp [hρ₁, h1]
      obtain ⟨ρ', h', v₁, v₂, f'⟩ := ih (r - (s + 1)) (by omega) (s + 1) ρ₁ e0 e1 e2
      refine ⟨ρ', BigStep.whileNormal (by rw [hs, hr]; exact hc)
        (BigStep.seqNormal (BigStep.assign _ _ _) (BigStep.assign _ _ _)) h', ?_, ?_, ?_⟩
      · have hl : loop s r = loop (s + 1) (r - (s + 1)) := by rw [loop]; simp [hc]
        rw [v₁, hl]
      · have hl : loop s r = loop (s + 1) (r - (s + 1)) := by rw [loop]; simp [hc]
        rw [v₂, hl]
      · intro v hv1 hv2
        rw [f' v hv1 hv2, hρ₁, Function.update_of_ne hv2, Function.update_of_ne hv1]
    · refine ⟨ρ, BigStep.whileFalse (by rw [hs, hr]; exact hc), ?_, ?_, fun _ _ _ => rfl⟩
      · rw [loop]; simp [hc, hs, hr]
      · rw [loop]; simp [hc, hr]

theorem unpairStep_spec {B i : ℕ} (hi : i < B) (ρ : ℕ → ℕ) :
    ∃ ρ', BigStep (unpairStep B i) ρ (.normal ρ') ∧ ρ' i = (decode (ρ (B + 1))).1 ∧
      ρ' (B + 1) = (decode (ρ (B + 1))).2 ∧ ρ' (B + 2) = 1 ∧
      ∀ v, v ≠ i → v ≠ B → v ≠ B + 1 → v ≠ B + 2 → ρ' v = ρ v := by
  set ρ₂ := Function.update (Function.update ρ B 0) (B + 2) 1 with hρ₂
  obtain ⟨ρ₃, h₃, v₃, w₃, f₃⟩ := unpairLoop_spec B (ρ (B + 1)) 0 ρ₂ (by simp [hρ₂])
    (by simp [hρ₂]) (by simp [hρ₂])
  refine ⟨_, BigStep.seqNormal (BigStep.assign _ _ _) (BigStep.seqNormal (BigStep.assign _ _ _)
    (BigStep.seqNormal h₃ (BigStep.assign _ _ _))), ?_, ?_, ?_, ?_⟩
  · simp only [Op.eval, Function.update_self]
    exact v₃
  · rw [Function.update_of_ne (by omega), w₃]; rfl
  · rw [Function.update_of_ne (by omega), f₃ _ (by omega) (by omega)]; simp [hρ₂]
  · intro v h1 h2 h3 h4
    rw [Function.update_of_ne h1, f₃ v h2 h3]; simp [hρ₂, Function.update_of_ne h2,
      Function.update_of_ne h4]


theorem unpairBody_spec {B : ℕ} (hB : 5 ≤ B) (x : ℕ) :
    BigStep (unpairBody B) (initFile ![x]) (.normal (initFile (dec5 x))) := by
  set ρ₁ := Function.update (initFile ![x]) (B + 1) (Op.eval (initFile ![x]) (.copy 0)) with hρ₁
  have r1 : ρ₁ (B + 1) = x := by simp [hρ₁, Op.eval, initFile]
  have z1 : ∀ v, v ≠ B + 1 → ρ₁ v = initFile ![x] v := fun v hv => Function.update_of_ne hv _ _
  obtain ⟨ρ₂, h₂, a₂, r₂, -, f₂⟩ := unpairStep_spec (B := B) (i := 0) (by omega) ρ₁
  obtain ⟨ρ₃, h₃, a₃, r₃, -, f₃⟩ := unpairStep_spec (B := B) (i := 1) (by omega) ρ₂
  obtain ⟨ρ₄, h₄, a₄, r₄, -, f₄⟩ := unpairStep_spec (B := B) (i := 2) (by omega) ρ₃
  obtain ⟨ρ₅, h₅, a₅, r₅, -, f₅⟩ := unpairStep_spec (B := B) (i := 3) (by omega) ρ₄
  rw [r1] at a₂ r₂; rw [r₂] at a₃ r₃; rw [r₃] at a₄ r₄; rw [r₄] at a₅ r₅
  have hfin : ∀ v, Function.update (Function.update (Function.update (Function.update ρ₅ 4
      (Op.eval ρ₅ (.copy (B + 1)))) B (Op.eval (Function.update ρ₅ 4 (Op.eval ρ₅ (.copy (B + 1))))
      (.const 0))) (B + 1) (Op.eval (Function.update (Function.update ρ₅ 4
      (Op.eval ρ₅ (.copy (B + 1)))) B (Op.eval (Function.update ρ₅ 4 (Op.eval ρ₅ (.copy (B + 1))))
      (.const 0))) (.const 0))) (B + 2) (Op.eval (Function.update (Function.update
      (Function.update ρ₅ 4 (Op.eval ρ₅ (.copy (B + 1)))) B (Op.eval (Function.update ρ₅ 4
      (Op.eval ρ₅ (.copy (B + 1)))) (.const 0))) (B + 1) (Op.eval (Function.update
      (Function.update ρ₅ 4 (Op.eval ρ₅ (.copy (B + 1)))) B (Op.eval (Function.update ρ₅ 4
      (Op.eval ρ₅ (.copy (B + 1)))) (.const 0))) (.const 0))) (.const 0)) v =
      initFile (dec5 x) v := by
    intro v
    simp only [Function.update_apply, Op.eval]
    by_cases hv2 : v = B + 2; · simp [hv2]; rw [initFile_of_le _ (by omega)]
    by_cases hv1 : v = B + 1; · simp [hv1]; rw [initFile_of_le _ (by omega)]
    by_cases hv0 : v = B; · simp [hv0]; rw [initFile_of_le _ (by omega)]
    by_cases h4 : v = 4
    · subst h4; simp [hv0, hv1, hv2, show (4 : ℕ) ≠ B by omega, r₅]
      rw [initFile_of_lt _ (by omega)]; rfl
    simp only [hv2, hv1, hv0, h4, ite_false]
    by_cases h3 : v = 3
    · subst h3; rw [a₅, initFile_of_lt _ (by omega)]; rfl
    rw [f₅ v h3 hv0 hv1 hv2]
    by_cases h2 : v = 2
    · subst h2; rw [a₄, initFile_of_lt _ (by omega)]; rfl
    rw [f₄ v h2 hv0 hv1 hv2]
    by_cases h1 : v = 1
    · subst h1; rw [a₃, initFile_of_lt _ (by omega)]; rfl
    rw [f₃ v h1 hv0 hv1 hv2]
    by_cases h0 : v = 0
    · subst h0; rw [a₂, initFile_of_lt _ (by omega)]; rfl
    rw [f₂ v h0 hv0 hv1 hv2, z1 v hv1, initFile_of_le _ (by omega), initFile_of_le _ (by omega)]
  have e := funext hfin
  rw [← e]
  exact BigStep.seqNormal (BigStep.assign _ _ _) (BigStep.seqNormal h₂ (BigStep.seqNormal h₃
    (BigStep.seqNormal h₄ (BigStep.seqNormal h₅ (BigStep.seqNormal (BigStep.assign _ _ _)
      (BigStep.seqNormal (BigStep.assign _ _ _) (BigStep.seqNormal (BigStep.assign _ _ _)
        (BigStep.assign _ _ _))))))))


theorem unpairProgram_body : unpairProgram.body = unpairBody precRegs := rfl

theorem unpairProgram_regsBound :
    unpairProgram.body.regsBound ≤ unpairProgram.bound := by decide +kernel

theorem five_le_precRegs : 5 ≤ precRegs := by decide +kernel

/-- **The prefix**: from the input `x` the run of the wrapper reaches the first relocated state
with the initial file of `M_prec` on `dec₅(x)`. -/
theorem wrapper_prefix_reaches (x : ℕ) :
    Reaches wrapper.toMachine ⟨0, initFile ![x]⟩ ⟨wrapperPrefix.length, initFile (dec5 x)⟩ := by
  have he : Embedded wrapper.toMachine 0 (code unpairProgram.bound unpairProgram.body 0 0 0) :=
    embedded_toMachine _ _
  have hsim : Sim unpairProgram.bound (initFile ![x]) (initFile ![x]) :=
    ⟨fun _ _ => rfl, fun i hi => initFile_of_le _ (by
      have := five_le_precRegs; simp only [unpairProgram] at hi; omega)⟩
  obtain ⟨σ', hσ', r⟩ := code_forward (unpairBody_spec five_le_precRegs x)
    (Stmt.regsBelow_of_regsBound unpairProgram_regsBound) he _ hsim
  have e : σ' = initFile (dec5 x) := by
    funext v
    by_cases hv : v < unpairProgram.bound
    · exact hσ'.1 v hv
    · rw [hσ'.2 v (by omega), initFile_of_le _ (by
        have := five_le_precRegs; simp only [unpairProgram] at hv; omega)]
  rw [e] at r
  refine r.state_eq ?_
  rw [wrapperPrefix, code_length, Nat.zero_add, unpairProgram_body]

/-! ### Relocation -/

theorem wrapper_length : wrapper.length = wrapperPrefix.length + precisionMachine.length := by
  simp [wrapper]

theorem wrapper_toMachine_shift (i : ℕ) :
    wrapper.toMachine (wrapperPrefix.length + i) =
      relocate wrapperPrefix.length (precisionMachine.toMachine i) := by
  by_cases hi : i < precisionMachine.length
  · rw [toMachine_of_lt _ (by rw [wrapper_length]; omega), toMachine_of_lt _ hi]
    simp only [wrapper]
    rw [List.getElem_append_right (by omega), List.getElem_map]
    simp only [Nat.add_sub_cancel_left]
  · rw [toMachine_of_le _ (by rw [wrapper_length]; omega), toMachine_of_le _ (by omega)]
    rfl

/-- The shift of a configuration by `|Π|`. -/
def shiftC (d : ℕ) (c : Config) : Config := ⟨d + c.state, c.regs⟩

theorem step_shift (i : ℕ) (σ : ℕ → ℕ) :
    step wrapper.toMachine ⟨wrapperPrefix.length + i, σ⟩ =
      (step precisionMachine.toMachine ⟨i, σ⟩).map (shiftC wrapperPrefix.length) := by
  unfold step
  simp only [wrapper_toMachine_shift]
  cases precisionMachine.toMachine i with
  | inc j x => simp [relocate, shiftC, Nat.add_comm]
  | dec j x y =>
    simp only [relocate]
    split_ifs <;> simp [shiftC, Nat.add_comm]
  | halt => rfl

theorem stepN_shift : ∀ (n i : ℕ) (σ : ℕ → ℕ),
    stepN wrapper.toMachine n ⟨wrapperPrefix.length + i, σ⟩ =
      (stepN precisionMachine.toMachine n ⟨i, σ⟩).map (shiftC wrapperPrefix.length)
  | 0, i, σ => rfl
  | n + 1, i, σ => by
    rw [stepN_succ, stepN_succ, step_shift]
    cases h : step precisionMachine.toMachine ⟨i, σ⟩ with
    | none => rfl
    | some c => simp only [Option.map_some, Option.bind_some, shiftC]; exact stepN_shift n _ _

theorem precisionMachine_pos : 0 < precisionMachine.length := by
  rw [precisionMachine, lower_length]; omega

theorem precisionMachine_last :
    precisionMachine.toMachine (precisionMachine.length - 1) = .halt := by
  have := (lower_embedded precisionProgram).2.2.2
  rw [precisionMachine, lower_length, show precisionProgram.body.len + precisionProgram.regCount + 2 - 1
    = precisionProgram.body.len + precisionProgram.regCount + 1 by omega]
  exact this

/-- Relocation: the wrapper halts on `x` iff `M_prec` halts on `dec₅(x)`. -/
theorem wrapper_halts_iff_machine (x : ℕ) :
    wrapper.HaltsOn ![x] ↔ precisionMachine.HaltsOn (dec5 x) := by
  obtain ⟨k, hk⟩ := wrapper_prefix_reaches x
  have hpos := precisionMachine_pos
  have hlast : wrapper.toMachine (wrapper.length - 1) = .halt := by
    rw [wrapper_length, show wrapperPrefix.length + precisionMachine.length - 1 =
      wrapperPrefix.length + (precisionMachine.length - 1) by omega, wrapper_toMachine_shift,
      precisionMachine_last]; rfl
  constructor
  · rintro ⟨t, c, ht, hs⟩
    obtain ⟨hkt, h'⟩ := halts_after hk ht (by rw [hs]; exact hlast)
    unfold ReachesIn at h'
    have := stepN_shift (t - k) 0 (initFile (dec5 x))
    rw [Nat.add_zero] at this
    rw [this] at h'
    cases h0 : stepN precisionMachine.toMachine (t - k) ⟨0, initFile (dec5 x)⟩ with
    | none => rw [h0] at h'; cases h'
    | some c₀ =>
      rw [h0] at h'
      simp only [Option.map_some, Option.some.injEq] at h'
      refine ⟨t - k, c₀, h0, ?_⟩
      rw [← h', wrapper_length] at hs
      simp only [shiftC] at hs
      generalize wrapperPrefix.length = d at *
      generalize precisionMachine.length = m at *
      omega
  · rintro ⟨t, c₀, ht, hs⟩
    have h1 := stepN_shift t 0 (initFile (dec5 x))
    rw [Nat.add_zero, ht, Option.map_some] at h1
    refine ⟨k + t, shiftC wrapperPrefix.length c₀, hk.trans h1, ?_⟩
    have hw := wrapper_length
    clear h1 ht hk
    generalize wrapperPrefix.length = d at hw ⊢
    generalize wrapper.length = w at hw ⊢
    generalize precisionMachine.length = m at hw hs hpos ⊢
    simp only [shiftC]
    omega

/-- **Correctness of the wrapper**: `𝒲` halts on `x` iff `accepts(dec₅(x))`. -/
theorem wrapper_halts_iff (x : ℕ) : wrapper.HaltsOn ![x] ↔ accepts (dec5 x) :=
  (wrapper_halts_iff_machine x).trans (precisionMachine_halts_iff (dec5 x))

/-- `𝒲` halts on `enc₅(c)` iff `accepts(c)`. -/
theorem wrapper_halts_encode (c : Fin 5 → ℕ) :
    wrapper.HaltsOn ![encode5 (c 0) (c 1) (c 2) (c 3) (c 4)] ↔ accepts c := by
  rw [wrapper_halts_iff, dec5_encode5]

end ZInQ.Compiler.IR
