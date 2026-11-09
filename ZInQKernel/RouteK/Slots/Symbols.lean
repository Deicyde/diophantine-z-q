import Mathlib

/-!
# Route K slots: residue bits

`docs/research/slot-k.md`, Notation: for an odd prime `p` and `x` prime to `p`, `[x/p] ∈ 𝔽₂` is
`0` if `x` is a square mod `p` and `1` otherwise; `λ_p = [-1/p]` and `μ_p = [2/p]`.
This file defines the bit `legBit p x`, relates it to `legendreSym`, and states quadratic
reciprocity in the form the note uses: `[p/q] + [q/p] = λ_p λ_q` for distinct odd primes.
-/

namespace ZInQ.RouteK

open Classical in
/-- `[a/p] ∈ 𝔽₂`: `0` if `a` is a square mod `p`, `1` otherwise. The note uses it only for `a`
prime to `p`; for `p ∣ a` it is `0`. -/
noncomputable def legBit (p : ℕ) (a : ℤ) : ZMod 2 := if IsSquare (a : ZMod p) then 0 else 1

/-- `λ_p = [-1/p]`. -/
noncomputable def lamBit (p : ℕ) : ZMod 2 := legBit p (-1)

/-- `μ_p = [2/p]`. -/
noncomputable def muBit (p : ℕ) : ZMod 2 := legBit p 2

theorem legBit_eq_zero_or_one (p : ℕ) (a : ℤ) : legBit p a = 0 ∨ legBit p a = 1 := by
  unfold legBit; split_ifs <;> simp

/-- The bit depends only on the residue class. -/
theorem legBit_congr {p : ℕ} {a b : ℤ} (h : a ≡ b [ZMOD p]) : legBit p a = legBit p b := by
  unfold legBit
  rw [(ZMod.intCast_eq_intCast_iff a b p).mpr h]

section Prime

variable {p : ℕ} [Fact p.Prime]

theorem legBit_eq_zero_iff {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    legBit p a = 0 ↔ legendreSym p a = 1 := by
  rw [legendreSym.eq_one_iff p ha, legBit]
  split_ifs with h <;> simp [h]

theorem legBit_eq_one_iff {a : ℤ} : legBit p a = 1 ↔ legendreSym p a = -1 := by
  rw [legendreSym.eq_neg_one_iff p, legBit]
  split_ifs with h <;> simp [h]

/-- The Legendre symbol of `a` prime to `p` is `(-1)^[a/p]`. -/
theorem legendreSym_eq_ite_legBit {a : ℤ} (ha : (a : ZMod p) ≠ 0) :
    legendreSym p a = if legBit p a = 0 then 1 else -1 := by
  rcases legBit_eq_zero_or_one p a with h | h
  · simp only [h, ite_true]; exact (legBit_eq_zero_iff ha).mp h
  · simp only [h, show (1 : ZMod 2) ≠ 0 by decide, ite_false]; exact legBit_eq_one_iff.mp h

/-- Prescribing the bit is prescribing the Legendre symbol. -/
theorem legBit_eq_iff_legendreSym {a : ℤ} (ha : (a : ZMod p) ≠ 0) (b : ZMod 2) :
    legBit p a = b ↔ legendreSym p a = if b = 0 then 1 else -1 := by
  rw [legendreSym_eq_ite_legBit ha]
  rcases legBit_eq_zero_or_one p a with h | h <;> rw [h] <;>
    rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl <;> norm_num

/-- Multiplicativity: `[ab/p] = [a/p] + [b/p]` for `a, b` prime to `p`. -/
theorem legBit_mul {a b : ℤ} (ha : (a : ZMod p) ≠ 0) (hb : (b : ZMod p) ≠ 0) :
    legBit p (a * b) = legBit p a + legBit p b := by
  have hab : ((a * b : ℤ) : ZMod p) ≠ 0 := by push_cast; exact mul_ne_zero ha hb
  have h := legendreSym.mul p a b
  rw [legendreSym_eq_ite_legBit hab, legendreSym_eq_ite_legBit ha,
    legendreSym_eq_ite_legBit hb] at h
  rcases legBit_eq_zero_or_one p a with h1 | h1 <;>
    rcases legBit_eq_zero_or_one p b with h2 | h2 <;>
    rcases legBit_eq_zero_or_one p (a * b) with h3 | h3 <;> simp only [h1, h2, h3] at h ⊢ <;>
    first | decide | norm_num at h

/-- `λ_p = [p ≡ 3 (mod 4)]`. -/
theorem lamBit_eq (p : ℕ) [Fact p.Prime] : lamBit p = if p % 4 = 3 then 1 else 0 := by
  rw [lamBit, legBit, show ((-1 : ℤ) : ZMod p) = -1 by push_cast; rfl]
  have := ZMod.exists_sq_eq_neg_one_iff (p := p)
  by_cases h : p % 4 = 3
  · simp only [show ¬ IsSquare (-1 : ZMod p) by rw [this]; exact not_not.mpr h, h, ite_true,
      ite_false]
  · simp only [this.mpr h, h, ite_true, ite_false]

/-- `μ_p = [p ≡ 3, 5 (mod 8)]` for an odd prime `p`. -/
theorem muBit_eq (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    muBit p = if p % 8 = 3 ∨ p % 8 = 5 then 1 else 0 := by
  rw [muBit, legBit, show ((2 : ℤ) : ZMod p) = 2 by push_cast; rfl]
  have h := ZMod.exists_sq_eq_two_iff hp2
  have hodd : p % 2 = 1 := (Nat.Prime.eq_two_or_odd Fact.out).resolve_left hp2
  by_cases h35 : p % 8 = 3 ∨ p % 8 = 5
  · have : ¬ IsSquare (2 : ZMod p) := by rw [h]; omega
    simp only [this, h35, ite_true, ite_false]
  · have : IsSquare (2 : ZMod p) := by rw [h]; omega
    simp only [this, h35, ite_true, ite_false]

/-- Multiplicativity over a finite product: `[∏ f i/p] = Σ [f i/p]` when every `f i` is prime to
`p`. -/
theorem legBit_prod {ι : Type*} (s : Finset ι) (f : ι → ℤ) (hf : ∀ i ∈ s, (f i : ZMod p) ≠ 0) :
    legBit p (∏ i ∈ s, f i) = ∑ i ∈ s, legBit p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty, Finset.sum_empty, legBit, Int.cast_one]
    simp [IsSquare.one]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    have hs : ((∏ j ∈ s, f j : ℤ) : ZMod p) ≠ 0 := by
      push_cast
      exact Finset.prod_ne_zero_iff.mpr fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [legBit_mul (hf i (Finset.mem_insert_self _ _)) hs,
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

end Prime

theorem odd_prime_mod_four {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : p % 4 = 1 ∨ p % 4 = 3 := by
  have := (Nat.Prime.eq_one_or_self_of_dvd hp 2)
  rcases hp.eq_two_or_odd with h | h
  · exact absurd h hp2
  · omega

theorem natCast_zmod_ne_zero_of_prime_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ((q : ℤ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd_natCast]
  exact fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)

/-- **Quadratic reciprocity in bits**: for distinct odd primes `p, q`,
`[q/p] + [p/q] = λ_p λ_q`. -/
theorem legBit_reciprocity {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p ≠ q) : legBit p q + legBit q p = lamBit p * lamBit q := by
  have := Fact.mk hp
  have := Fact.mk hq
  have h1 := natCast_zmod_ne_zero_of_prime_ne hp hq hpq
  have h2 := natCast_zmod_ne_zero_of_prime_ne hq hp (Ne.symm hpq)
  have e1 := legendreSym_eq_ite_legBit h1
  have e2 := legendreSym_eq_ite_legBit h2
  rw [lamBit_eq p, lamBit_eq q]
  have key : (p % 4 = 1 ∨ q % 4 = 1) → legendreSym q p = legendreSym p q := by
    rintro (h | h)
    · exact legendreSym.quadratic_reciprocity_one_mod_four h hq2
    · exact (legendreSym.quadratic_reciprocity_one_mod_four h hp2).symm
  rcases odd_prime_mod_four hp hp2 with hp4 | hp4 <;>
    rcases odd_prime_mod_four hq hq2 with hq4 | hq4
  · have r := key (Or.inl hp4)
    rw [e1, e2] at r; rw [hp4, hq4]
    rcases legBit_eq_zero_or_one p q with b1 | b1 <;>
      rcases legBit_eq_zero_or_one q p with b2 | b2 <;> simp only [b1, b2] at r ⊢ <;>
      first | decide | norm_num at r
  · have r := key (Or.inl hp4)
    rw [e1, e2] at r; rw [hp4, hq4]
    rcases legBit_eq_zero_or_one p q with b1 | b1 <;>
      rcases legBit_eq_zero_or_one q p with b2 | b2 <;> simp only [b1, b2] at r ⊢ <;>
      first | decide | norm_num at r
  · have r := key (Or.inr hq4)
    rw [e1, e2] at r; rw [hp4, hq4]
    rcases legBit_eq_zero_or_one p q with b1 | b1 <;>
      rcases legBit_eq_zero_or_one q p with b2 | b2 <;> simp only [b1, b2] at r ⊢ <;>
      first | decide | norm_num at r
  · have r := legendreSym.quadratic_reciprocity_three_mod_four hp4 hq4
    rw [e1, e2] at r; rw [hp4, hq4]
    rcases legBit_eq_zero_or_one p q with b1 | b1 <;>
      rcases legBit_eq_zero_or_one q p with b2 | b2 <;> simp only [b1, b2] at r ⊢ <;>
      first | decide | norm_num at r

/-- Reverse symbols for a glue prime `r ≡ 1 (mod 4)`: `[y/r] = [r/y]`. -/
theorem legBit_symm_of_one_mod_four {r y : ℕ} (hr : r.Prime) (hy : y.Prime) (hy2 : y ≠ 2)
    (hry : r ≠ y) (hr4 : r % 4 = 1) : legBit r y = legBit y r := by
  have := Fact.mk hr
  have h := legBit_reciprocity hr hy (by omega) hy2 hry
  simp only [lamBit_eq r, show r % 4 ≠ 3 by omega, ite_false, zero_mul] at h
  revert h
  rcases legBit_eq_zero_or_one r y with h1 | h1 <;>
    rcases legBit_eq_zero_or_one y r with h2 | h2 <;>
    rw [h1, h2] <;> decide

/-- Reverse symbols for a prime `q ≡ 3 (mod 4)`: `[y/q] = [q/y] + λ_y`. -/
theorem legBit_symm_of_three_mod_four {q y : ℕ} (hq : q.Prime) (hy : y.Prime) (hy2 : y ≠ 2)
    (hqy : q ≠ y) (hq4 : q % 4 = 3) : legBit q y = legBit y q + lamBit y := by
  have := Fact.mk hq
  have h := legBit_reciprocity hq hy (by omega) hy2 hqy
  simp only [lamBit_eq q, hq4, ite_true, one_mul] at h
  revert h
  rw [lamBit]
  rcases legBit_eq_zero_or_one q y with h1 | h1 <;>
    rcases legBit_eq_zero_or_one y q with h2 | h2 <;>
    rcases legBit_eq_zero_or_one y (-1) with h3 | h3 <;> rw [h1, h2, h3] <;> decide

end ZInQ.RouteK
