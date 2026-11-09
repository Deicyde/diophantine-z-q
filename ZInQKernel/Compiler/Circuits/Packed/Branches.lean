import ZInQKernel.Compiler.Circuits.Packed.Masks
import ZInQKernel.Compiler.Circuits.RegisterMachine

/-!
# Branch histories and indicator digits

1. For zero-one digit sequences `σ, ν` in base `B = 2^b`, with `S = ∑ σ_t B^t` and
   `N = ∑ ν_t B^t`: `V = S AND N` and `S = V + W` iff `V = ∑ σ_t ν_t B^t` and
   `W = ∑ σ_t (1 - ν_t) B^t` (`branch_split`).
2. If in every slot exactly one state digit is `1` (`σ_i(t) = [i = i_t]`), the packed indicators
   `A_j`, `C_j` and `I_i` of the packed-history construction have the slot digits
   `[p_{i_t} = inc(j, ·)]`, `[p_{i_t} = dec(j, ·, ·)] ν_j(t)` and "the instruction at `i_t` takes,
   at time `t`, a branch to `i`", all in `{0, 1}` (`indicator_digits`). The halt instruction
   contributes to none of them.

(Blueprint: `compiler/natural/packed/packed-branches.md`.)
-/

namespace ZInQ.Compiler.Packed

open Finset RM

/-- **Item 1: branch histories.** -/
theorem branch_split {b q : ℕ} (σ ν : ℕ → ℕ) (hσ : ∀ t ≤ q, σ t ≤ 1) (hν : ∀ t ≤ q, ν t ≤ 1)
    (hb : 1 ≤ b) (V W : ℕ) :
    (V = Nat.land (∑ t ∈ range (q + 1), σ t * (2 ^ b) ^ t) (∑ t ∈ range (q + 1), ν t * (2 ^ b) ^ t) ∧
        ∑ t ∈ range (q + 1), σ t * (2 ^ b) ^ t = V + W) ↔
      (V = ∑ t ∈ range (q + 1), σ t * ν t * (2 ^ b) ^ t ∧
        W = ∑ t ∈ range (q + 1), σ t * (1 - ν t) * (2 ^ b) ^ t) := by
  simp only [← pack_def]
  have h2 : (2 : ℕ) ≤ 2 ^ b := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hland : Nat.land (pack (2 ^ b) σ q) (pack (2 ^ b) ν q) =
      pack (2 ^ b) (fun t => σ t * ν t) q := by
    show pack (2 ^ b) σ q &&& pack (2 ^ b) ν q = _
    rw [land_pack (fun t ht => by have := hσ t ht; omega) (fun t ht => by have := hν t ht; omega)]
    refine pack_congr fun t ht => ?_
    have := hσ t ht
    have := hν t ht
    interval_cases (σ t) <;> interval_cases (ν t) <;> rfl
  have hsplit : pack (2 ^ b) σ q =
      pack (2 ^ b) (fun t => σ t * ν t) q + pack (2 ^ b) (fun t => σ t * (1 - ν t)) q := by
    rw [pack_add]
    refine pack_congr fun t ht => ?_
    have := hν t ht
    interval_cases (ν t) <;> simp
  rw [hland]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, hsplit⟩

/-! ### Indicator digits -/

/-- `p_i = inc(j, ·)`. -/
def incOn (p : Program) (j i : ℕ) : Prop := ∃ x, p[i]? = some (.inc j x)

/-- `p_i = dec(j, ·, ·)`. -/
def decOn (p : Program) (j i : ℕ) : Prop := ∃ x y, p[i]? = some (.dec j x y)

/-- `p_{i'} = inc(·, i)`. -/
def incTo (p : Program) (i' i : ℕ) : Prop := ∃ j, p[i']? = some (.inc j i)

/-- `p_{i'} = dec(·, i, ·)`: the nonzero branch of `i'` goes to `i`. -/
def nzTo (p : Program) (i' i : ℕ) : Prop := ∃ j y, p[i']? = some (.dec j i y)

/-- `p_{i'} = dec(·, ·, i)`: the zero branch of `i'` goes to `i`. -/
def zTo (p : Program) (i' i : ℕ) : Prop := ∃ j x, p[i']? = some (.dec j x i)

/-- The register of a sub instruction (`0` for other instructions). -/
def decReg (p : Program) (i : ℕ) : ℕ :=
  match p[i]? with
  | some (.dec j _ _) => j
  | _ => 0

instance (p : Program) (j i : ℕ) : Decidable (incOn p j i) := by
  unfold incOn
  match p[i]? with
  | some (.inc j' x) => exact if h : j' = j then isTrue ⟨x, by rw [h]⟩ else isFalse (by simp [h])
  | some (.dec _ _ _) => exact isFalse (by simp)
  | some .halt => exact isFalse (by simp)
  | none => exact isFalse (by simp)

instance (p : Program) (j i : ℕ) : Decidable (decOn p j i) := by
  unfold decOn
  match p[i]? with
  | some (.dec j' x y) =>
    exact if h : j' = j then isTrue ⟨x, y, by rw [h]⟩ else isFalse (by simp [h])
  | some (.inc _ _) => exact isFalse (by simp)
  | some .halt => exact isFalse (by simp)
  | none => exact isFalse (by simp)

instance (p : Program) (i' i : ℕ) : Decidable (incTo p i' i) := by
  unfold incTo
  match p[i']? with
  | some (.inc j x) => exact if h : x = i then isTrue ⟨j, by rw [h]⟩ else isFalse (by simp [h])
  | some (.dec _ _ _) => exact isFalse (by simp)
  | some .halt => exact isFalse (by simp)
  | none => exact isFalse (by simp)

instance (p : Program) (i' i : ℕ) : Decidable (nzTo p i' i) := by
  unfold nzTo
  match p[i']? with
  | some (.dec j x y) =>
    exact if h : x = i then isTrue ⟨j, y, by rw [h]⟩ else isFalse (by simp [h])
  | some (.inc _ _) => exact isFalse (by simp)
  | some .halt => exact isFalse (by simp)
  | none => exact isFalse (by simp)

instance (p : Program) (i' i : ℕ) : Decidable (zTo p i' i) := by
  unfold zTo
  match p[i']? with
  | some (.dec j x y) =>
    exact if h : y = i then isTrue ⟨j, x, by rw [h]⟩ else isFalse (by simp [h])
  | some (.inc _ _) => exact isFalse (by simp)
  | some .halt => exact isFalse (by simp)
  | none => exact isFalse (by simp)

/-- `A_j = ∑_{p_i = inc(j, ·)} S_i`. -/
def incSum (p : Program) (S : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ range p.length, if incOn p j i then S i else 0

/-- `C_j = ∑_{p_i = dec(j, ·, ·)} V_i`. -/
def decSum (p : Program) (V : ℕ → ℕ) (j : ℕ) : ℕ :=
  ∑ i ∈ range p.length, if decOn p j i then V i else 0

/-- `I_i`: the sum of `S_{i'}` over `p_{i'} = inc(·, i)`, of `V_{i'}` over `p_{i'} = dec(·, i, ·)`
and of `W_{i'}` over `p_{i'} = dec(·, ·, i)`. -/
def inSum (p : Program) (S V W : ℕ → ℕ) (i : ℕ) : ℕ :=
  ∑ i' ∈ range p.length,
    ((if incTo p i' i then S i' else 0) + (if nzTo p i' i then V i' else 0) +
      (if zTo p i' i then W i' else 0))

/-- The slot digit of `I_i` when the instruction at state `a` is active with nonzero digit
`n` of its register. -/
def inDigit (p : Program) (a i n : ℕ) : ℕ :=
  (if incTo p a i then 1 else 0) + (if nzTo p a i then n else 0) + (if zTo p a i then 1 - n else 0)

theorem not_incTo_and_nzTo {p : Program} {a i : ℕ} (h1 : incTo p a i) (h2 : nzTo p a i) :
    False := by
  obtain ⟨j, h1⟩ := h1; obtain ⟨j', y, h2⟩ := h2; rw [h1] at h2; cases h2

theorem not_incTo_and_zTo {p : Program} {a i : ℕ} (h1 : incTo p a i) (h2 : zTo p a i) :
    False := by
  obtain ⟨j, h1⟩ := h1; obtain ⟨j', x, h2⟩ := h2; rw [h1] at h2; cases h2

theorem inDigit_le_one (p : Program) (a i : ℕ) {n : ℕ} (hn : n ≤ 1) : inDigit p a i n ≤ 1 := by
  unfold inDigit
  by_cases h1 : incTo p a i
  · have h2 : ¬ nzTo p a i := fun h => not_incTo_and_nzTo h1 h
    have h3 : ¬ zTo p a i := fun h => not_incTo_and_zTo h1 h
    simp [h1, h2, h3]
  · by_cases h2 : nzTo p a i <;> by_cases h3 : zTo p a i <;> simp [h1, h2, h3] <;> omega

theorem decOn_decReg_of_nzTo {p : Program} {i' i : ℕ} (h : nzTo p i' i) :
    decOn p (decReg p i') i' := by
  obtain ⟨j, y, h⟩ := h; exact ⟨i, y, by simp [decReg, h]⟩

theorem decOn_decReg_of_zTo {p : Program} {i' i : ℕ} (h : zTo p i' i) :
    decOn p (decReg p i') i' := by
  obtain ⟨j, x, h⟩ := h; exact ⟨x, i, by simp [decReg, h]⟩

theorem sum_select {m a : ℕ} (ha : a < m) (g : ℕ → ℕ) :
    ∑ i ∈ range m, (if a = i then g i else 0) = g a := by
  rw [Finset.sum_ite_eq]; simp [ha]

/-- **Item 2: indicator digits.** If in every slot `t ≤ q` exactly the state `act t < m` is
active, the packed indicators have the stated zero-one digits. -/
theorem indicator_digits {B q : ℕ} (p : Program) (act : ℕ → ℕ) (ν : ℕ → ℕ → ℕ)
    (hact : ∀ t ≤ q, act t < p.length) (S V W : ℕ → ℕ)
    (hS : ∀ i < p.length, S i = ∑ t ∈ range (q + 1), (if act t = i then 1 else 0) * B ^ t)
    (hV : ∀ i < p.length, ∀ j, decOn p j i →
      V i = ∑ t ∈ range (q + 1), (if act t = i then 1 else 0) * ν j t * B ^ t)
    (hW : ∀ i < p.length, ∀ j, decOn p j i →
      W i = ∑ t ∈ range (q + 1), (if act t = i then 1 else 0) * (1 - ν j t) * B ^ t) :
    (∀ j, incSum p S j = ∑ t ∈ range (q + 1), (if incOn p j (act t) then 1 else 0) * B ^ t) ∧
    (∀ j, decSum p V j = ∑ t ∈ range (q + 1), (if decOn p j (act t) then ν j t else 0) * B ^ t) ∧
    (∀ i, inSum p S V W i =
      ∑ t ∈ range (q + 1), inDigit p (act t) i (ν (decReg p (act t)) t) * B ^ t) := by
  simp only [← pack_def] at hS hV hW ⊢
  refine ⟨fun j => ?_, fun j => ?_, fun i => ?_⟩
  · unfold incSum
    rw [Finset.sum_congr rfl fun i hi => show (if incOn p j i then S i else 0) =
        pack B (fun t => if act t = i then (if incOn p j i then 1 else 0) else 0) q by
      rw [hS i (Finset.mem_range.1 hi)]
      by_cases h : incOn p j i
      · rw [ite_eq_left h]; exact pack_congr fun t _ => by simp [h]
      · rw [ite_eq_right h]; exact (pack_const_zero B q).symm.trans (pack_congr fun t _ => by simp [h]),
      pack_sum]
    exact pack_congr fun t ht => by rw [sum_select (hact t ht) (fun i => if incOn p j i then 1 else 0)]
  · unfold decSum
    rw [Finset.sum_congr rfl fun i hi => show (if decOn p j i then V i else 0) =
        pack B (fun t => if act t = i then (if decOn p j i then ν j t else 0) else 0) q by
      by_cases h : decOn p j i
      · rw [ite_eq_left h, hV i (Finset.mem_range.1 hi) j h]
        exact pack_congr fun t _ => by by_cases hat : act t = i <;> simp [h, hat]
      · rw [ite_eq_right h]; exact (pack_const_zero B q).symm.trans (pack_congr fun t _ => by simp [h]),
      pack_sum]
    exact pack_congr fun t ht => by
      rw [sum_select (hact t ht) (fun i => if decOn p j i then ν j t else 0)]
  · unfold inSum
    rw [Finset.sum_congr rfl fun i' hi' => show
        ((if incTo p i' i then S i' else 0) + (if nzTo p i' i then V i' else 0) +
          (if zTo p i' i then W i' else 0)) =
        pack B (fun t => if act t = i' then inDigit p i' i (ν (decReg p i') t) else 0) q by
      have hi'' := Finset.mem_range.1 hi'
      have e1 : (if incTo p i' i then S i' else 0) =
          pack B (fun t => if incTo p i' i then (if act t = i' then 1 else 0) else 0) q := by
        by_cases h : incTo p i' i
        · rw [ite_eq_left h]; exact (hS i' hi'').trans (pack_congr fun t _ => by simp [h])
        · rw [ite_eq_right h]; exact (pack_const_zero B q).symm.trans (pack_congr fun t _ => by simp [h])
      have e2 : (if nzTo p i' i then V i' else 0) = pack B (fun t => if nzTo p i' i then
          (if act t = i' then 1 else 0) * ν (decReg p i') t else 0) q := by
        by_cases h : nzTo p i' i
        · rw [ite_eq_left h]; exact (hV i' hi'' _ (decOn_decReg_of_nzTo h)).trans (pack_congr fun t _ => by simp [h])
        · rw [ite_eq_right h]; exact (pack_const_zero B q).symm.trans (pack_congr fun t _ => by simp [h])
      have e3 : (if zTo p i' i then W i' else 0) = pack B (fun t => if zTo p i' i then
          (if act t = i' then 1 else 0) * (1 - ν (decReg p i') t) else 0) q := by
        by_cases h : zTo p i' i
        · rw [ite_eq_left h]; exact (hW i' hi'' _ (decOn_decReg_of_zTo h)).trans (pack_congr fun t _ => by simp [h])
        · rw [ite_eq_right h]; exact (pack_const_zero B q).symm.trans (pack_congr fun t _ => by simp [h])
      rw [e1, e2, e3, pack_add, pack_add]
      refine pack_congr fun t _ => ?_
      by_cases hat : act t = i' <;> simp [hat, inDigit],
      pack_sum]
    exact pack_congr fun t ht => by
      rw [sum_select (hact t ht) (fun i' => inDigit p i' i (ν (decReg p i') t))]

end ZInQ.Compiler.Packed
