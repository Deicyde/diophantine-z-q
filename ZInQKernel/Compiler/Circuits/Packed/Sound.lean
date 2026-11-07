import ZInQKernel.Compiler.Circuits.Packed.Step
import ZInQKernel.Compiler.Circuits.Packed.StateSelection
import ZInQKernel.Compiler.Circuits.Packed.NonzeroIndicator
import ZInQKernel.Compiler.Circuits.Packed.Transitions

/-!
# Soundness of the packed-history construction

`PackedConditions p r k a q c K B T F D R N S V W` is the formula of the packed-history
construction with every macro read as its relation (masks as bit inclusion, bitAnd as bitwise
conjunction, power as exponentiation, lt as strict inequality), at natural values of its fresh
variables. If it holds, `p` accepts `a`, and its accepting run has exactly `q` steps.

(Blueprint: `compiler/natural/packed/packed-sound.md`.)
-/

namespace ZInQ.Compiler.Packed

open Finset RM

/-- The packed-history conditions: the conjunction of items 1–7 of the construction with every
macro replaced by its relation. `V_i, W_i` matter only for sub instructions. -/
structure PackedConditions (p : Program) (r k : ℕ) (a : Fin k → ℕ) (q c K B T F D : ℕ)
    (R N S V W : ℕ → ℕ) : Prop where
  c_pos : 0 < c
  hK : K = 2 ^ c
  hB : B = 4 * K
  m_lt : p.length < B
  hT : T = B ^ q
  inputs_lt : ∀ i : Fin k, a i < K
  hF : B * F + 1 = F + B * T
  hD : D + F = K * F
  sumS : ∑ i ∈ range p.length, S i = F
  lastS : S (p.length - 1) = T
  maskS : ∀ i < p.length, Nat.land (S i) F = S i
  maskR : ∀ j < r, Nat.land (R j) D = R j
  ltR : ∀ j < r, R j < T
  nonzero : ∀ j < r, K * N j = Nat.land (R j + D) (K * F)
  branch : ∀ i < p.length, ∀ j, decOn p j i → V i = Nat.land (S i) (N j) ∧ S i = V i + W i
  regEq : ∀ j < r, R j + B * decSum p V j = initFile a j + B * R j + B * incSum p S j
  stateEq : ∀ i < p.length, S i = (if i = 0 then 1 else 0) + B * inSum p S V W i

/-- Run data read off a solution: the active state and the register values at each time. -/
structure RunData (p : Program) (r k : ℕ) (a : Fin k → ℕ) (q : ℕ) (act : ℕ → ℕ)
    (ρ : ℕ → ℕ → ℕ) : Prop where
  act_lt : ∀ t ≤ q, act t < p.length
  act_zero : act 0 = 0
  act_last : ∀ t ≤ q, act t = p.length - 1 ↔ t = q
  init : ∀ j < r, ρ j 0 = initFile a j
  final : ∀ j < r, ρ j q = 0
  state_step : ∀ t < q, ∀ i < p.length,
    (if act (t + 1) = i then 1 else 0) = inDigit p (act t) i (nzDigit (ρ (decReg p (act t)) t))
  reg_step : ∀ t < q, ∀ j < r,
    ρ j (t + 1) + (if decOn p j (act t) then nzDigit (ρ j t) else 0) =
      ρ j t + (if incOn p j (act t) then 1 else 0)

theorem decReg_lt {p : Program} {r : ℕ} (hp : p.Valid r) (hr : 0 < r) {a : ℕ}
    (ha : a < p.length - 1) : decReg p a < r := by
  have hvalid := hp.valid a (by omega)
  have hget : p[a]? = some p[a] := List.getElem?_eq_getElem (by omega)
  unfold decReg
  rw [hget]
  generalize p[a] = ins at hvalid
  cases ins with
  | dec j x y => exact hvalid.1
  | inc j x => exact hr
  | halt => exact absurd hvalid id

/-- The configuration at time `t` of the decoded run. -/
def runConfig (r : ℕ) (act : ℕ → ℕ) (ρ : ℕ → ℕ → ℕ) (t : ℕ) : Config :=
  ⟨act t, fun j => if j < r then ρ j t else 0⟩

/-- **Run reconstruction.** Run data yield the accepting run of `q` steps. -/
theorem RunData.stepN {p : Program} {r k : ℕ} (hp : p.Valid r) (hk : k ≤ r) (hr : 0 < r)
    {a : Fin k → ℕ} {q : ℕ} {act : ℕ → ℕ} {ρ : ℕ → ℕ → ℕ} (h : RunData p r k a q act ρ) :
    ∀ t ≤ q, RM.stepN p.toMachine t ⟨0, initFile a⟩ = some (runConfig r act ρ t) := by
  have h0 : (⟨0, initFile a⟩ : Config) = runConfig r act ρ 0 := by
    simp only [runConfig, h.act_zero, Config.mk.injEq, true_and]
    funext j
    split_ifs with hj
    · exact (h.init j hj).symm
    · exact initFile_of_le a (by omega)
  intro t ht
  induction t with
  | zero => rw [stepN_zero, h0]
  | succ t ih =>
    rw [stepN_succ', ih (by omega), Option.bind_some]
    have hat : act t < p.length - 1 := by
      have h1 := h.act_lt t (by omega)
      have h2 : act t ≠ p.length - 1 := fun he => by have := (h.act_last t (by omega)).1 he; omega
      omega
    refine (step_iff_digits hp hat (fun j hj => by simp; omega) (fun j hj => by simp; omega)
      (h.act_lt (t + 1) ht)).2 ⟨fun i hi => ?_, fun j hj => ?_⟩
    · have hd := decReg_lt hp hr hat
      simp only [ite_eq_left hd]
      exact h.state_step t (by omega) i hi
    · simp only [ite_eq_left hj]
      exact h.reg_step t (by omega) j hj

theorem RunData.accepts {p : Program} {r k : ℕ} (hp : p.Valid r) (hk : k ≤ r) (hr : 0 < r)
    {a : Fin k → ℕ} {q : ℕ} {act : ℕ → ℕ} {ρ : ℕ → ℕ → ℕ} (h : RunData p r k a q act ρ) :
    ∃ cfg, RM.stepN p.toMachine q ⟨0, initFile a⟩ = some cfg ∧ cfg.state = p.length - 1 ∧
      ∀ j, cfg.regs j = 0 := by
  refine ⟨runConfig r act ρ q, h.stepN hp hk hr q le_rfl, (h.act_last q le_rfl).2 rfl, fun j => ?_⟩
  simp only [runConfig]
  split_ifs with hj
  · exact h.final j hj
  · rfl

theorem decOn_lt {p : Program} {r : ℕ} (hp : p.Valid r) {i j : ℕ} (hi : i < p.length)
    (h : decOn p j i) : j < r := by
  obtain ⟨x, y, hxy⟩ := h
  have hget : p[i]? = some p[i] := List.getElem?_eq_getElem hi
  rw [hget, Option.some.injEq] at hxy
  by_cases hlast : i = p.length - 1
  · have := hp.last; simp only [← hlast] at this; rw [hxy] at this; cases this
  · have := hp.valid i (by omega); rw [hxy] at this; exact this.1

/-- **Decoding.** A solution of the packed conditions yields run data. -/
theorem decode {p : Program} {r k : ℕ} (hp : p.Valid r) {a : Fin k → ℕ}
    {q c K B T F D : ℕ} {R N S V W : ℕ → ℕ} (h : PackedConditions p r k a q c K B T F D R N S V W) :
    ∃ act ρ, RunData p r k a q act ρ := by
  have hm0 : 0 < p.length := hp.pos
  have hKpos : 1 ≤ K := by rw [h.hK]; exact Nat.one_le_two_pow
  have hKB : K < B := by rw [h.hB]; omega
  have hB2 : B = 2 ^ (c + 2) := by rw [h.hB, h.hK, four_mul_two_pow]
  obtain ⟨⟨hFq, -⟩, hRm, hSm⟩ := packed_masks h.c_pos h.hK h.hB h.hT h.hF h.hD
  have hDq : D = (K - 1) * F := by have := h.hD; rw [Nat.sub_one_mul]; omega
  -- register and state digits
  let ρ : ℕ → ℕ → ℕ := fun j t => digit B (R j) t
  let σ : ℕ → ℕ → ℕ := fun i t => digit B (S i) t
  have hρ : ∀ j < r, (∀ t ≤ q, ρ j t < K) ∧ ρ j q = 0 ∧ R j = ∑ t ∈ range (q + 1), ρ j t * B ^ t := by
    intro j hj
    obtain ⟨ρ', h1, h2, h3⟩ := (hRm (R j)).1 ⟨h.maskR j hj, h.ltR j hj⟩
    rw [← pack_def] at h3
    have hd : ∀ t ≤ q, ρ j t = ρ' t := fun t ht => by
      show digit B (R j) t = ρ' t
      rw [h3]; exact digit_pack (fun t ht => lt_trans (h1 t ht) hKB) ht
    refine ⟨fun t ht => hd t ht ▸ h1 t ht, (hd q le_rfl).trans h2, ?_⟩
    rw [← pack_def, h3]; exact pack_congr fun t ht => (hd t ht).symm
  have hσ : ∀ i < p.length, (∀ t ≤ q, σ i t ≤ 1) ∧ S i = ∑ t ∈ range (q + 1), σ i t * B ^ t := by
    intro i hi
    obtain ⟨σ', h1, h3⟩ := (hSm (S i)).1 (h.maskS i hi)
    rw [← pack_def] at h3
    have hd : ∀ t ≤ q, σ i t = σ' t := fun t ht => by
      show digit B (S i) t = σ' t
      rw [h3]; exact digit_pack (fun t ht => by have := h1 t ht; omega) ht
    refine ⟨fun t ht => hd t ht ▸ h1 t ht, ?_⟩
    rw [← pack_def, h3]; exact pack_congr fun t ht => (hd t ht).symm
  -- one active state
  have hsel := (one_active_state h.m_lt hm0 σ fun i hi t ht => (hσ i hi).1 t ht).1 ⟨by
      rw [← hFq, ← h.sumS]
      exact Finset.sum_congr rfl fun i hi => ((hσ i (Finset.mem_range.1 hi)).2).symm, by
      rw [← (hσ _ (by omega)).2, h.lastS, h.hT]⟩
  let act : ℕ → ℕ := fun t =>
    if hex : ∃ i, i < p.length ∧ σ i t = 1 then Nat.find hex else 0
  have hact : ∀ t ≤ q, act t < p.length ∧ ∀ i < p.length, σ i t = if act t = i then 1 else 0 := by
    intro t ht
    obtain ⟨i₀, hi₀, huniq⟩ := hsel.1 t ht
    have hex : ∃ i, i < p.length ∧ σ i t = 1 := ⟨i₀, hi₀⟩
    have hspec := Nat.find_spec hex
    have hact_eq : act t = Nat.find hex := dite_eq_left hex
    refine ⟨hact_eq ▸ hspec.1, fun i hi => ?_⟩
    rw [hact_eq]
    split_ifs with heq
    · rw [← heq]; exact hspec.2
    · have h1 := (hσ i hi).1 t ht
      by_contra hne
      have hi1 : σ i t = 1 := by omega
      exact heq ((huniq _ hspec).trans (huniq i ⟨hi, hi1⟩).symm)
  -- nonzero indicators
  let ν : ℕ → ℕ → ℕ := fun j t => nzDigit (ρ j t)
  have hν : ∀ j < r, N j = ∑ t ∈ range (q + 1), ν j t * B ^ t := by
    intro j hj
    obtain ⟨h1, -, h3⟩ := hρ j hj
    have := (nonzero_indicator h.c_pos h.hK h.hB hFq hDq (ρ j) h1).2 (N j)
    rw [← h3] at this
    exact this.1 (h.nonzero j hj)
  -- branch histories
  have hbr : ∀ i < p.length, ∀ j, decOn p j i →
      V i = ∑ t ∈ range (q + 1), (if act t = i then 1 else 0) * ν j t * B ^ t ∧
      W i = ∑ t ∈ range (q + 1), (if act t = i then 1 else 0) * (1 - ν j t) * B ^ t := by
    intro i hi j hj
    have hjr := decOn_lt hp hi hj
    obtain ⟨hb1, hb2⟩ := h.branch i hi j hj
    have key := (branch_split (b := c + 2) (q := q) (σ i) (ν j) (hσ i hi).1
      (fun t _ => nzDigit_le_one _) (by omega) (V i) (W i)).1
      ⟨by rw [← hB2, ← (hσ i hi).2, ← hν j hjr]; exact hb1, by rw [← hB2, ← (hσ i hi).2]; exact hb2⟩
    rw [← hB2] at key
    refine ⟨key.1.trans (Finset.sum_congr rfl fun t ht => ?_), key.2.trans (Finset.sum_congr rfl fun t ht => ?_)⟩
    · rw [(hact t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))).2 i hi]
    · rw [(hact t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))).2 i hi]
  -- indicator digits
  obtain ⟨hinc, hdec, hin⟩ := indicator_digits (B := B) (q := q) p act ν
    (fun t ht => (hact t ht).1) S V W
    (fun i hi => (hσ i hi).2.trans (Finset.sum_congr rfl fun t ht => by
      rw [(hact t (Nat.lt_succ_iff.mp (Finset.mem_range.mp ht))).2 i hi]))
    (fun i hi j hj => (hbr i hi j hj).1) (fun i hi j hj => (hbr i hi j hj).2)
  -- transitions
  have hregs : ∀ j < r, ρ j 0 = initFile a j ∧
      (∀ t < q, ρ j (t + 1) + (if decOn p j (act t) then ν j t else 0) =
        ρ j t + (if incOn p j (act t) then 1 else 0)) := by
    intro j hj
    obtain ⟨h1, -, h3⟩ := hρ j hj
    have hι : initFile a j < K := by
      unfold initFile; split_ifs with hjk
      · exact h.inputs_lt _
      · omega
    have := (packed_register_iff hKB (ρ j) (fun t => if incOn p j (act t) then 1 else 0)
      (fun t => if decOn p j (act t) then ν j t else 0) h1
      (fun t _ => by by_cases hc : incOn p j (act t) <;> simp [hc])
      (fun t _ => by by_cases hc : decOn p j (act t) <;> simp [hc, ν, nzDigit_le_one]) hι).1
      (by rw [← h3, ← hinc j, ← hdec j]; exact h.regEq j hj)
    exact ⟨this.1, this.2.1⟩
  have hstates : ∀ i < p.length, σ i 0 = (if i = 0 then 1 else 0) ∧
      ∀ t < q, σ i (t + 1) = inDigit p (act t) i (ν (decReg p (act t)) t) := by
    intro i hi
    have := (packed_state_iff (B := B) (q := q) (e := if i = 0 then 1 else 0) (by omega) (σ i)
      (fun t => inDigit p (act t) i (ν (decReg p (act t)) t)) (hσ i hi).1
      (fun t _ => inDigit_le_one _ _ _ (nzDigit_le_one _)) (by by_cases hc : i = 0 <;> simp [hc])).1
      (by rw [← (hσ i hi).2, ← hin i]; exact h.stateEq i hi)
    exact ⟨this.1, this.2.1⟩
  refine ⟨act, ρ, fun t ht => (hact t ht).1, ?_, fun t ht => ?_, fun j hj => (hregs j hj).1,
    fun j hj => (hρ j hj).2.1, fun t ht i hi => ?_, fun t ht j hj => (hregs j hj).2 t ht⟩
  · have h1 := (hstates 0 hm0).1
    rw [(hact 0 (Nat.zero_le _)).2 0 hm0] at h1
    simpa using h1
  · rw [← hsel.2 t ht, (hact t ht).2 _ (by omega)]
    simp
  · rw [← (hact (t + 1) ht).2 i hi]
    exact (hstates i hi).2 t ht

/-- **Soundness of the packed-history construction.** If the packed conditions hold for some
natural values of the fresh variables, `p` accepts `a`, with an accepting run of exactly `q`
steps. -/
theorem packed_sound {p : Program} {r k : ℕ} (hp : p.Valid r) (hk1 : 1 ≤ k) (hkr : k ≤ r)
    {a : Fin k → ℕ} {q c K B T F D : ℕ} {R N S V W : ℕ → ℕ}
    (h : PackedConditions p r k a q c K B T F D R N S V W) :
    ∃ cfg, RM.stepN p.toMachine q ⟨0, initFile a⟩ = some cfg ∧ cfg.state = p.length - 1 ∧
      ∀ j, cfg.regs j = 0 := by
  obtain ⟨act, ρ, hrun⟩ := decode hp h
  exact hrun.accepts hp hkr (by omega)

theorem packed_sound_accepts {p : Program} {r k : ℕ} (hp : p.Valid r) (hk1 : 1 ≤ k)
    (hkr : k ≤ r) {a : Fin k → ℕ} {q c K B T F D : ℕ} {R N S V W : ℕ → ℕ}
    (h : PackedConditions p r k a q c K B T F D R N S V W) : p.Accepts a := by
  obtain ⟨cfg, h1, h2, h3⟩ := packed_sound hp hk1 hkr h
  exact ⟨q, cfg, h1, h2, h3⟩

end ZInQ.Compiler.Packed
