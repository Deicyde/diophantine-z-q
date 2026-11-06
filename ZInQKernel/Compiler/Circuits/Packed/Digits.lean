import Mathlib

/-!
# Base-`B` packing of digit sequences

`pack B f q = ∑_{t ≤ q} f t · B^t`. We prove the uniqueness of base-`B` digits, the linearity of
packing, the splitting `pack B f (q+1) = f 0 + B · pack B (f ∘ succ) q`, the expansion of every
number below `B^{q+1}` in base `B`, and, for `B = 2^b`, that bitwise conjunction is computed
digitwise.
-/

namespace ZInQ.Compiler.Packed

open Finset

/-- `pack B f q = ∑_{t ≤ q} f t · B^t`. -/
def pack (B : ℕ) (f : ℕ → ℕ) (q : ℕ) : ℕ := ∑ t ∈ range (q + 1), f t * B ^ t

theorem pack_def (B : ℕ) (f : ℕ → ℕ) (q : ℕ) : pack B f q = ∑ t ∈ range (q + 1), f t * B ^ t :=
  rfl

@[simp] theorem pack_zero (B : ℕ) (f : ℕ → ℕ) : pack B f 0 = f 0 := by simp [pack]

theorem pack_succ (B : ℕ) (f : ℕ → ℕ) (q : ℕ) :
    pack B f (q + 1) = f 0 + B * pack B (fun t => f (t + 1)) q := by
  rw [pack, Finset.sum_range_succ', pack, Finset.mul_sum]
  simp only [pow_zero, mul_one]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

/-- The last digit splits off at the top. -/
theorem pack_succ_top (B : ℕ) (f : ℕ → ℕ) (q : ℕ) :
    pack B f (q + 1) = pack B f q + f (q + 1) * B ^ (q + 1) := by
  rw [pack, Finset.sum_range_succ, ← pack]

theorem pack_congr {B : ℕ} {f g : ℕ → ℕ} {q : ℕ} (h : ∀ t ≤ q, f t = g t) :
    pack B f q = pack B g q :=
  Finset.sum_congr rfl fun t ht => by rw [h t (by simpa [Nat.lt_succ_iff] using ht)]

theorem pack_add (B : ℕ) (f g : ℕ → ℕ) (q : ℕ) :
    pack B f q + pack B g q = pack B (fun t => f t + g t) q := by
  simp only [pack, ← Finset.sum_add_distrib, add_mul]

theorem mul_pack (B c : ℕ) (f : ℕ → ℕ) (q : ℕ) : c * pack B f q = pack B (fun t => c * f t) q := by
  simp only [pack, Finset.mul_sum, mul_assoc]

theorem pack_sum {ι : Type*} (B : ℕ) (s : Finset ι) (f : ι → ℕ → ℕ) (q : ℕ) :
    ∑ i ∈ s, pack B (f i) q = pack B (fun t => ∑ i ∈ s, f i t) q := by
  simp only [pack, Finset.sum_mul]
  exact Finset.sum_comm

theorem pack_const_zero (B q : ℕ) : pack B (fun _ => 0) q = 0 := by simp [pack]

theorem pack_lt {B : ℕ} {f : ℕ → ℕ} {q : ℕ} (hf : ∀ t ≤ q, f t < B) : pack B f q < B ^ (q + 1) := by
  induction q generalizing f with
  | zero => simpa using hf 0 le_rfl
  | succ q ih =>
    rw [pack_succ]
    have h1 := ih (f := fun t => f (t + 1)) fun t ht => hf (t + 1) (by omega)
    have h0 := hf 0 (by omega)
    rw [pow_succ' B (q + 1)]
    nlinarith

theorem pack_mod {B : ℕ} {f : ℕ → ℕ} (hf : f 0 < B) (q : ℕ) : pack B f q % B = f 0 := by
  cases q with
  | zero => simpa using Nat.mod_eq_of_lt hf
  | succ q =>
    rw [pack_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hf]

theorem pack_div {B : ℕ} {f : ℕ → ℕ} (hB : 0 < B) (hf : f 0 < B) (q : ℕ) :
    pack B f (q + 1) / B = pack B (fun t => f (t + 1)) q := by
  rw [pack_succ, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hf, zero_add]

/-- **Uniqueness of base-`B` digits.** -/
theorem pack_inj {B : ℕ} {f g : ℕ → ℕ} {q : ℕ} (hf : ∀ t ≤ q, f t < B) (hg : ∀ t ≤ q, g t < B)
    (h : pack B f q = pack B g q) : ∀ t ≤ q, f t = g t := by
  induction q generalizing f g with
  | zero => intro t ht; simpa [show t = 0 by omega] using h
  | succ q ih =>
    have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hf 0 (by omega))
    have h0 : f 0 = g 0 := by
      rw [← pack_mod (hf 0 (by omega)) (q + 1), ← pack_mod (hg 0 (by omega)) (q + 1), h]
    have h1 : pack B (fun t => f (t + 1)) q = pack B (fun t => g (t + 1)) q := by
      rw [← pack_div hB (hf 0 (by omega)), ← pack_div hB (hg 0 (by omega)), h]
    intro t ht
    rcases t with _ | t
    · exact h0
    · exact ih (fun t ht => hf (t + 1) (by omega)) (fun t ht => hg (t + 1) (by omega)) h1 t
        (by omega)

/-- The base-`B` digits of a natural number. -/
def digit (B R t : ℕ) : ℕ := R / B ^ t % B

theorem digit_lt {B : ℕ} (hB : 0 < B) (R t : ℕ) : digit B R t < B := Nat.mod_lt _ hB

/-- **Base-`B` expansion.** Every number below `B^{q+1}` is the packing of its digits. -/
theorem eq_pack_digit {B : ℕ} (hB : 0 < B) {q R : ℕ} (hR : R < B ^ (q + 1)) :
    R = pack B (digit B R) q := by
  induction q generalizing R with
  | zero => simp [digit, Nat.mod_eq_of_lt (by simpa using hR)]
  | succ q ih =>
    rw [pack_succ]
    have hq : R / B < B ^ (q + 1) := by
      rw [Nat.div_lt_iff_lt_mul hB, ← pow_succ]; exact hR
    have := ih hq
    have hd : (fun t => digit B R (t + 1)) = digit B (R / B) := by
      funext t; simp [digit, Nat.div_div_eq_div_mul, pow_succ, mul_comm]
    rw [hd, ← this]
    simp only [digit, pow_zero, Nat.div_one]
    exact (Nat.mod_add_div R B).symm

theorem digit_pack {B : ℕ} {f : ℕ → ℕ} {q : ℕ} (hf : ∀ t ≤ q, f t < B) {t : ℕ} (ht : t ≤ q) :
    digit B (pack B f q) t = f t := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hf 0 (Nat.zero_le _))
  have h := eq_pack_digit hB (pack_lt hf)
  exact (pack_inj hf (fun t _ => digit_lt hB _ t) h t ht).symm

/-! ### Bitwise conjunction of packed numbers in base `2^b` -/

theorem land_split {b a a' m m' : ℕ} (ha : a < 2 ^ b) (ha' : a' < 2 ^ b) :
    (a + 2 ^ b * m) &&& (a' + 2 ^ b * m') = (a &&& a') + 2 ^ b * (m &&& m') := by
  apply Nat.eq_of_testBit_eq
  intro j
  have hlt : a &&& a' < 2 ^ b := Nat.and_lt_two_pow a ha'
  rw [add_comm a, add_comm a', add_comm (a &&& a'), Nat.testBit_and,
    Nat.testBit_two_pow_mul_add _ ha, Nat.testBit_two_pow_mul_add _ ha',
    Nat.testBit_two_pow_mul_add _ hlt]
  split_ifs <;> simp [Nat.testBit_and]

/-- **Digitwise conjunction.** In base `2^b`, the conjunction of two packed numbers with digits
below `2^b` is the packing of the digitwise conjunctions. -/
theorem land_pack {b : ℕ} {f g : ℕ → ℕ} {q : ℕ} (hf : ∀ t ≤ q, f t < 2 ^ b)
    (hg : ∀ t ≤ q, g t < 2 ^ b) :
    pack (2 ^ b) f q &&& pack (2 ^ b) g q = pack (2 ^ b) (fun t => f t &&& g t) q := by
  induction q generalizing f g with
  | zero => simp
  | succ q ih =>
    rw [pack_succ, pack_succ, pack_succ, land_split (hf 0 (by omega)) (hg 0 (by omega)),
      ih (fun t ht => hf (t + 1) (by omega)) (fun t ht => hg (t + 1) (by omega))]

end ZInQ.Compiler.Packed
