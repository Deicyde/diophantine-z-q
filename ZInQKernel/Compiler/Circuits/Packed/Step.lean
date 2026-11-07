import ZInQKernel.Compiler.Circuits.Packed.Branches

/-!
# One machine step in slot digits

For a valid program and a non-final state `a`, a step from `(a, ρ)` to `(a', ρ')` is equivalent
to the slot equations of the packed construction: the incoming digit of every state `i` is
`[a' = i]`, and every register satisfies `ρ'_j + γ_j = ρ_j + α_j` with the increment indicator
`α_j = [p_a = inc(j, ·)]` and the decrement indicator `γ_j = [p_a = dec(j, ·, ·)] [ρ_j > 0]`.

(Helper for `packed-sound.md` and `packed-complete.md`.)
-/

namespace ZInQ.Compiler.Packed

open RM

/-- The nonzero indicator digit of a register value. -/
def nzDigit (n : ℕ) : ℕ := if 0 < n then 1 else 0

theorem nzDigit_le_one (n : ℕ) : nzDigit n ≤ 1 := by unfold nzDigit; split_ifs <;> omega

theorem step_iff_digits {p : Program} {r : ℕ} (hp : p.Valid r) {a : ℕ}
    (ha : a < p.length - 1) {ρ ρ' : ℕ → ℕ} (hρ : ∀ j, r ≤ j → ρ j = 0)
    (hρ' : ∀ j, r ≤ j → ρ' j = 0) {a' : ℕ} (ha' : a' < p.length) :
    step p.toMachine ⟨a, ρ⟩ = some ⟨a', ρ'⟩ ↔
      (∀ i < p.length, (if a' = i then 1 else 0) = inDigit p a i (nzDigit (ρ (decReg p a)))) ∧
      (∀ j < r, ρ' j + (if decOn p j a then nzDigit (ρ j) else 0) =
        ρ j + (if incOn p j a then 1 else 0)) := by
  have hvalid := hp.valid a (by omega)
  have hget : p[a]? = some p[a] := List.getElem?_eq_getElem (by omega)
  simp only [step, toMachine_of_lt p (show a < p.length by omega)]
  generalize hins : p[a] = ins at hvalid hget
  cases ins with
  | halt => exact absurd hvalid id
  | inc j x =>
    obtain ⟨hj, hx⟩ := hvalid
    have hinc : ∀ j', incOn p j' a ↔ j' = j := fun j' => by simp [incOn, hget, eq_comm]
    have hdec : ∀ j', ¬ decOn p j' a := fun j' => by simp [decOn, hget]
    have hin : ∀ i, inDigit p a i 0 = if x = i then 1 else 0 := fun i => by
      simp [inDigit, incTo, nzTo, zTo, hget]
    have hin' : ∀ i n, inDigit p a i n = if x = i then 1 else 0 := fun i n => by
      simp [inDigit, incTo, nzTo, zTo, hget]
    simp only [Option.some.injEq, Config.mk.injEq, hin', hdec, ite_false, add_zero]
    constructor
    · rintro ⟨rfl, rfl⟩
      refine ⟨fun i _ => rfl, fun j' hj' => ?_⟩
      by_cases h : j' = j
      · subst h; simp [hinc]
      · simp [Function.update_of_ne h, (hinc j').not.2 h]
    · rintro ⟨h1, h2⟩
      have hxa : x = a' := by
        have := h1 a' ha'; simp at this
        exact this
      refine ⟨hxa, funext fun j' => ?_⟩
      by_cases hj'r : j' < r
      · have := h2 j' hj'r
        by_cases h : j' = j
        · subst h; simp only [Function.update_self]; simp [hinc] at this; omega
        · rw [Function.update_of_ne h]; simp [(hinc j').not.2 h] at this; omega
      · rw [hρ' j' (by omega), Function.update_of_ne (by omega), hρ j' (by omega)]
  | dec j x y =>
    obtain ⟨hj, hx, hy⟩ := hvalid
    have hinc : ∀ j', ¬ incOn p j' a := fun j' => by simp [incOn, hget]
    have hdec : ∀ j', decOn p j' a ↔ j' = j := fun j' => by simp [decOn, hget, eq_comm]
    have hreg : decReg p a = j := by simp [decReg, hget]
    have hin : ∀ i n, inDigit p a i n =
        (if x = i then n else 0) + (if y = i then 1 - n else 0) := fun i n => by
      simp [inDigit, incTo, nzTo, zTo, hget]
    simp only [hin, hreg, hinc, ite_false, add_zero]
    by_cases hz : ρ j = 0
    · simp only [hz, ite_true, Option.some.injEq, Config.mk.injEq, nzDigit, lt_irrefl, ite_false,
        tsub_zero]
      constructor
      · rintro ⟨rfl, rfl⟩
        refine ⟨fun i _ => by split_ifs <;> simp_all, fun j' hj' => ?_⟩
        by_cases h : j' = j
        · subst h; simp [hdec, hz]
        · simp [(hdec j').not.2 h]
      · rintro ⟨h1, h2⟩
        have hya : y = a' := by
          have := h1 a' ha'; simp at this
          exact this
        refine ⟨hya, funext fun j' => ?_⟩
        by_cases hj'r : j' < r
        · have := h2 j' hj'r
          by_cases h : j' = j
          · subst h; simp [hdec, hz] at this ⊢; omega
          · simp [(hdec j').not.2 h] at this; omega
        · rw [hρ' j' (by omega), hρ j' (by omega)]
    · have hpos : 0 < ρ j := Nat.pos_of_ne_zero hz
      simp only [hz, ite_false, Option.some.injEq, Config.mk.injEq, nzDigit, hpos, ite_true,
        Nat.sub_self]
      constructor
      · rintro ⟨rfl, rfl⟩
        refine ⟨fun i _ => by split_ifs <;> simp_all, fun j' hj' => ?_⟩
        by_cases h : j' = j
        · subst h; simp [hdec, hpos]; omega
        · simp [(hdec j').not.2 h, Function.update_of_ne h]
      · rintro ⟨h1, h2⟩
        have hxa : x = a' := by
          have := h1 a' ha'; simp at this
          exact this
        refine ⟨hxa, funext fun j' => ?_⟩
        by_cases hj'r : j' < r
        · have := h2 j' hj'r
          by_cases h : j' = j
          · subst h; simp [hdec, hpos] at this ⊢; omega
          · rw [Function.update_of_ne h]; simp [(hdec j').not.2 h] at this; omega
        · rw [hρ' j' (by omega), Function.update_of_ne (by omega), hρ j' (by omega)]

end ZInQ.Compiler.Packed
