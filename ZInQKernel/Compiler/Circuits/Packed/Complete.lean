import ZInQKernel.Compiler.Circuits.Packed.Sound

/-!
# Completeness of the packed-history construction

If `p` (valid for `r` registers, `1 ≤ k ≤ r`) accepts `a`, the packed conditions hold for some
natural values of the fresh variables: with the accepting run of `q` steps, choose `c ≥ 1` with
`2^c` above every register value and with `4 · 2^c > m`, and pack the run.

(Blueprint: `compiler/natural/packed/packed-complete.md`.)
-/

namespace ZInQ.Compiler.Packed

open Finset RM

theorem inDigit_halt {p : Program} {r : ℕ} (hp : p.Valid r) (i n : ℕ) :
    inDigit p (p.length - 1) i n = 0 := by
  have hget : p[p.length - 1]? = some .halt := by
    rw [List.getElem?_eq_getElem (by have := hp.pos; omega), hp.last]
  simp [inDigit, incTo, nzTo, zTo, hget]

theorem not_incOn_halt {p : Program} {r : ℕ} (hp : p.Valid r) (j : ℕ) :
    ¬ incOn p j (p.length - 1) := by
  have hget : p[p.length - 1]? = some .halt := by
    rw [List.getElem?_eq_getElem (by have := hp.pos; omega), hp.last]
  simp [incOn, hget]

theorem not_decOn_halt {p : Program} {r : ℕ} (hp : p.Valid r) (j : ℕ) :
    ¬ decOn p j (p.length - 1) := by
  have hget : p[p.length - 1]? = some .halt := by
    rw [List.getElem?_eq_getElem (by have := hp.pos; omega), hp.last]
  simp [decOn, hget]

theorem decReg_of_decOn {p : Program} {i j : ℕ} (h : decOn p j i) : decReg p i = j := by
  obtain ⟨x, y, h⟩ := h; simp [decReg, h]

/-- Registers at or above `r` stay zero along a run of a valid program. -/
theorem step_regs_high {p : Program} {r : ℕ} (hp : p.Valid r) {c c' : Config}
    (hc : c.state < p.length) (h : step p.toMachine c = some c') (hr : ∀ j, r ≤ j → c.regs j = 0) :
    ∀ j, r ≤ j → c'.regs j = 0 := by
  intro j hj
  unfold step at h
  rw [toMachine_of_lt p hc] at h
  by_cases hlast : c.state = p.length - 1
  · rw [show p[c.state] = .halt by simp only [hlast]; exact hp.last] at h; cases h
  have hvalid := hp.valid c.state (by omega)
  generalize p[c.state] = ins at h hvalid
  cases ins with
  | halt => cases h
  | inc j' x =>
    simp only [Option.some.injEq] at h; subst h
    simp only [Function.update_of_ne (show j ≠ j' by have := hvalid.1; omega)]; exact hr j hj
  | dec j' x y =>
    dsimp only at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h
    · exact hr j hj
    · simp only [Function.update_of_ne (show j ≠ j' by have := hvalid.1; omega)]; exact hr j hj

theorem step_state_lt {p : Program} {r : ℕ} (hp : p.Valid r) {c c' : Config}
    (h : step p.toMachine c = some c') : c.state < p.length - 1 ∧ c'.state < p.length := by
  have hc : c.state < p.length := by
    by_contra hge
    rw [step, toMachine_of_le p (by omega)] at h; cases h
  have hne : c.state ≠ p.length - 1 := by
    intro he
    rw [step, (hp.toMachine_eq_halt_iff hc).2 he] at h; cases h
  refine ⟨by omega, ?_⟩
  have hvalid := hp.valid c.state (by omega)
  unfold step at h
  rw [toMachine_of_lt p hc] at h
  generalize p[c.state] = ins at h hvalid
  cases ins with
  | halt => cases h
  | inc j x => simp only [Option.some.injEq] at h; subst h; exact hvalid.2
  | dec j x y =>
    dsimp only at h
    split_ifs at h <;> simp only [Option.some.injEq] at h <;> subst h
    · exact hvalid.2.2
    · exact hvalid.2.1

/-- **Completeness of the packed-history construction.** If `p` accepts `a`, the packed
conditions hold for some natural values of the fresh variables. -/
theorem packed_complete {p : Program} {r k : ℕ} (hp : p.Valid r) (_hk1 : 1 ≤ k) (hkr : k ≤ r)
    {a : Fin k → ℕ} (h : p.Accepts a) :
    ∃ q c K B T F D : ℕ, ∃ R N S V W : ℕ → ℕ,
      PackedConditions p r k a q c K B T F D R N S V W := by
  obtain ⟨q, cfgq, hq, hstate, hregs⟩ := h
  have hm0 : 0 < p.length := hp.pos
  let c0 : Config := ⟨0, initFile a⟩
  let conf : ℕ → Config := fun t => (RM.stepN p.toMachine t c0).getD c0
  have hconf : ∀ t ≤ q, RM.stepN p.toMachine t c0 = some (conf t) := by
    intro t ht
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le ht
    rw [stepN_add] at hq
    cases h' : RM.stepN p.toMachine t c0 with
    | none => rw [h'] at hq; cases hq
    | some x => simp [conf, h']
  have hstep : ∀ t < q, step p.toMachine (conf t) = some (conf (t + 1)) := by
    intro t ht
    have := hconf (t + 1) ht
    rw [stepN_succ', hconf t (by omega), Option.bind_some] at this
    exact this
  have hconfq : conf q = cfgq := by
    have := hconf q le_rfl; rw [hq] at this; exact (Option.some.inj this).symm
  have hconf0 : conf 0 = c0 := by simp [conf]
  let act : ℕ → ℕ := fun t => (conf t).state
  let ρ : ℕ → ℕ → ℕ := fun j t => (conf t).regs j
  have hact_lt : ∀ t < q, act t < p.length - 1 ∧ act (t + 1) < p.length :=
    fun t ht => step_state_lt hp (hstep t ht)
  have hactq : act q = p.length - 1 := by simp only [act, hconfq, hstate]
  have hact_le : ∀ t ≤ q, act t < p.length := by
    intro t ht
    rcases Nat.lt_or_eq_of_le ht with h | rfl
    · have := (hact_lt t h).1; omega
    · rw [hactq]; omega
  have hact_last : ∀ t ≤ q, act t = p.length - 1 ↔ t = q := by
    intro t ht
    constructor
    · intro he
      by_contra hne
      have := (hact_lt t (by omega)).1; omega
    · rintro rfl; exact hactq
  have hhigh : ∀ t ≤ q, ∀ j, r ≤ j → ρ j t = 0 := by
    intro t ht
    induction t with
    | zero => intro j hj; simp only [ρ, hconf0, c0]; exact initFile_of_le a (by omega)
    | succ t ih =>
      exact step_regs_high hp (hact_le t (by omega)) (hstep t (by omega)) (ih (by omega))
  have hdig : ∀ t < q,
      (∀ i < p.length, (if act (t + 1) = i then 1 else 0) =
        inDigit p (act t) i (nzDigit (ρ (decReg p (act t)) t))) ∧
      (∀ j < r, ρ j (t + 1) + (if decOn p j (act t) then nzDigit (ρ j t) else 0) =
        ρ j t + (if incOn p j (act t) then 1 else 0)) := by
    intro t ht
    have := hstep t ht
    have e1 : conf t = ⟨act t, fun j => ρ j t⟩ := rfl
    have e2 : conf (t + 1) = ⟨act (t + 1), fun j => ρ j (t + 1)⟩ := rfl
    rw [e1, e2] at this
    exact (step_iff_digits hp (hact_lt t ht).1 (hhigh t (by omega)) (hhigh (t + 1) ht)
      (hact_lt t ht).2).1 this
  -- the digit capacity
  let M : ℕ := ∑ t ∈ range (q + 1), ∑ j ∈ range r, ρ j t
  have hρM : ∀ t ≤ q, ∀ j < r, ρ j t ≤ M := by
    intro t ht j hj
    calc ρ j t ≤ ∑ j ∈ range r, ρ j t :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hj)
      _ ≤ M := Finset.single_le_sum (f := fun t => ∑ j ∈ range r, ρ j t)
          (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (by omega))
  let c : ℕ := M + p.length + 1
  have hc2 : c < 2 ^ c := Nat.lt_two_pow_self
  let K : ℕ := 2 ^ c
  let B : ℕ := 4 * K
  have hKpos : 1 ≤ K := Nat.one_le_two_pow
  have hρK : ∀ t ≤ q, ∀ j < r, ρ j t < K := fun t ht j hj => by
    have := hρM t ht j hj; show ρ j t < 2 ^ c; omega
  have hKB : K < B := by omega
  have hB2 : B = 2 ^ (c + 2) := by simp only [B, K]; rw [four_mul_two_pow]
  let T : ℕ := B ^ q
  let F : ℕ := ∑ t ∈ range (q + 1), B ^ t
  let D : ℕ := (K - 1) * F
  let σ : ℕ → ℕ → ℕ := fun i t => if act t = i then 1 else 0
  let ν : ℕ → ℕ → ℕ := fun j t => nzDigit (ρ j t)
  let R : ℕ → ℕ := fun j => ∑ t ∈ range (q + 1), ρ j t * B ^ t
  let N : ℕ → ℕ := fun j => ∑ t ∈ range (q + 1), ν j t * B ^ t
  let S : ℕ → ℕ := fun i => ∑ t ∈ range (q + 1), σ i t * B ^ t
  let V : ℕ → ℕ := fun i => ∑ t ∈ range (q + 1), σ i t * ν (decReg p i) t * B ^ t
  let W : ℕ → ℕ := fun i => ∑ t ∈ range (q + 1), σ i t * (1 - ν (decReg p i) t) * B ^ t
  have hF : B * F + 1 = F + B * T := by
    have := pack_one_geom B q
    simp only [pack, one_mul] at this
    simp only [F, T, ← pow_succ']
    exact this
  have hD : D + F = K * F := by simp only [D]; rw [Nat.sub_one_mul]; have := Nat.le_mul_of_pos_left F hKpos; omega
  obtain ⟨-, hRm, hSm⟩ := packed_masks (c := c) (by omega) rfl rfl rfl hF hD
  have hσ1 : ∀ i t, σ i t ≤ 1 := fun i t => by simp only [σ]; split_ifs <;> omega
  obtain ⟨hsum, hlast⟩ := (one_active_state (B := B) (q := q) (by omega) hm0 σ
    (fun i _ t _ => hσ1 i t)).2 ⟨fun t ht => ⟨act t, ⟨hact_le t ht, by simp [σ]⟩,
      fun i ⟨_, hi⟩ => by simp only [σ] at hi; split_ifs at hi with he; exact he.symm⟩,
      fun t ht => by simp only [σ]; rw [← hact_last t ht]; split_ifs <;> simp_all⟩
  obtain ⟨hinc, hdec, hin⟩ := indicator_digits (B := B) (q := q) p act ν hact_le S V W
    (fun i _ => rfl)
    (fun i _ j hj => by simp only [V, decReg_of_decOn hj]; rfl)
    (fun i _ j hj => by simp only [W, decReg_of_decOn hj]; rfl)
  refine ⟨q, c, K, B, T, F, D, R, N, S, V, W, ?_⟩
  exact {
    c_pos := by omega
    hK := rfl
    hB := rfl
    m_lt := by show p.length < 4 * 2 ^ c; omega
    hT := rfl
    inputs_lt := fun i => by
      have := hρK 0 (Nat.zero_le _) i (by omega)
      simp only [ρ, hconf0, c0] at this
      rwa [initFile_of_lt a i.isLt] at this
    hF := hF
    hD := hD
    sumS := hsum
    lastS := hlast
    maskS := fun i _ => (hSm (S i)).2 ⟨σ i, fun t _ => hσ1 i t, rfl⟩
    maskR := fun j hj => ((hRm (R j)).2 ⟨ρ j, fun t ht => hρK t ht j hj, by
      have := congrArg (fun c : Config => c.regs j) hconfq
      simp only [ρ, this, hregs], rfl⟩).1
    ltR := fun j hj => ((hRm (R j)).2 ⟨ρ j, fun t ht => hρK t ht j hj, by
      have := congrArg (fun c : Config => c.regs j) hconfq
      simp only [ρ, this, hregs], rfl⟩).2
    nonzero := fun j hj =>
      ((nonzero_indicator (c := c) (by omega) rfl rfl rfl rfl (ρ j)
        (fun t ht => hρK t ht j hj)).1).symm
    branch := fun i hi j hj => by
      have key := (branch_split (b := c + 2) (q := q) (σ i) (ν j) (fun t _ => hσ1 i t)
        (fun t _ => nzDigit_le_one _) (by omega) (V i) (W i)).2
        ⟨by simp only [V, decReg_of_decOn hj, ← hB2], by simp only [W, decReg_of_decOn hj, ← hB2]⟩
      rw [← hB2] at key
      exact key
    regEq := fun j hj => by
      have hι : initFile a j < K := by
        have := hρK 0 (Nat.zero_le _) j hj
        simp only [ρ, hconf0, c0] at this; exact this
      rw [hinc j, hdec j]
      refine (packed_register_iff hKB (ρ j) (fun t => if incOn p j (act t) then 1 else 0)
        (fun t => if decOn p j (act t) then ν j t else 0) (fun t ht => hρK t ht j hj)
        (fun t _ => by by_cases hc : incOn p j (act t) <;> simp [hc])
        (fun t _ => by by_cases hc : decOn p j (act t) <;> simp [hc, ν, nzDigit_le_one]) hι).2
        ⟨by simp [ρ, hconf0, c0], fun t ht => (hdig t ht).2 j hj, ?_⟩
      rw [hactq]
      have := congrArg (fun c : Config => c.regs j) hconfq
      simp [not_incOn_halt hp, not_decOn_halt hp, ρ, this, hregs]
    stateEq := fun i hi => by
      rw [hin i]
      refine (packed_state_iff (B := B) (q := q) (e := if i = 0 then 1 else 0) (by omega) (σ i)
        (fun t => inDigit p (act t) i (ν (decReg p (act t)) t)) (fun t _ => hσ1 i t)
        (fun t _ => inDigit_le_one _ _ _ (nzDigit_le_one _))
        (by by_cases hc : i = 0 <;> simp [hc])).2 ⟨?_, fun t ht => (hdig t ht).1 i hi, ?_⟩
      · simp [σ, act, hconf0, c0, eq_comm]
      · rw [hactq]; exact inDigit_halt hp _ _ }

end ZInQ.Compiler.Packed
