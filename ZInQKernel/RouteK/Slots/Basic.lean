import Mathlib
import ZInQKernel.Hypotheses.Pole

/-!
# Route K slots: admissible inputs, squarefree parts, `β` and `θ`

`docs/research/slot-k.md` §1.1. An input `B` is *admissible* when it satisfies the hypothesis of
`ZInQ.PoleCompleteness`. For a signed divisor `m` of 2730 the note puts `β = sqf(mB)` and
`θ = sqf(m(m - B))`, where `sqf` is the signed squarefree part of a nonzero rational: the unique
squarefree integer `d` with `x ∈ d · ℚ*²`.
-/

namespace ZInQ.RouteK

open scoped BigOperators

/-- `B` is **admissible**: its reduced denominator is a square, `0 < B < 1/2`, and
`v_p(B) ≥ 4` for `p ∈ S₀ = {2, 3, 5, 7, 13}`. This is the hypothesis of
`ZInQ.PoleCompleteness`, see `poleCompleteness_iff_admissible`. -/
def Admissible (B : ℚ) : Prop :=
  IsSquare B.den ∧ 0 < B ∧ B < 1 / 2 ∧ ∀ p ∈ poleS0, 4 ≤ padicValRat p B

theorem poleCompleteness_iff_admissible :
    PoleCompleteness ↔ ∀ B, Admissible B → PoleSoluble B :=
  ⟨fun h _ hB => h _ hB.1 hB.2.1 hB.2.2.1 hB.2.2.2, fun h B h1 h2 h3 h4 => h B ⟨h1, h2, h3, h4⟩⟩

/-- The squarefree part of a natural number: the product of the primes with odd exponent. -/
def sqfNat (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors with Odd (n.factorization p), p

/-- The signed squarefree part of an integer. -/
def sqfInt (N : ℤ) : ℤ := N.sign * sqfNat N.natAbs

/-- The signed squarefree part `sqf x` of a rational `x = num/den`: that of `num · den`, which
lies in the same square class as `x`. For `x ≠ 0` it is the unique squarefree integer `d` with
`x = d t²` for a rational `t` (`sqf_spec`, `sqf_eq_of_eq_mul_sq`). -/
def sqf (x : ℚ) : ℤ := sqfInt (x.num * x.den)

/-- `β = sqf(mB)`, for an input `B` and a multiplier `m` (a signed divisor of 2730). -/
def betaOf (B : ℚ) (m : ℤ) : ℤ := sqf (m * B)

/-- `θ = sqf(m(m - B))`, for an input `B` and a multiplier `m` (a signed divisor of 2730). -/
def thetaOf (B : ℚ) (m : ℤ) : ℤ := sqf (m * (m - B))

/-! ### The squarefree part -/

theorem sqfNat_squarefree (n : ℕ) : Squarefree (sqfNat n) := by
  unfold sqfNat
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq => ?_) fun p hp => ?_
  · simp only [Finset.coe_filter, Set.mem_ofPred_eq, Nat.mem_primeFactors] at hp hq
    simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes hp.1.1 hq.1.1).mpr hpq
  · exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).squarefree

theorem sqfNat_mul_sq {n : ℕ} (hn : n ≠ 0) : ∃ k : ℕ, k ≠ 0 ∧ n = sqfNat n * k ^ 2 := by
  refine ⟨∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2),
    Finset.prod_ne_zero_iff.mpr fun p hp =>
      pow_ne_zero _ (Nat.prime_of_mem_primeFactors hp).ne_zero, ?_⟩
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization, sqfNat, Finset.prod_filter, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← pow_mul]
  rcases Nat.even_or_odd (n.factorization p) with h | h
  · simp only [Nat.not_odd_iff_even.mpr h, ite_false, one_mul]
    rw [Nat.div_mul_cancel (even_iff_two_dvd.mp h)]
  · simp only [h, ite_true]
    conv_lhs => rw [← Nat.div_add_mod (n.factorization p) 2, Nat.odd_iff.mp h]
    rw [pow_succ, mul_comm 2, mul_comm]

/-- Two squarefree natural numbers in the same square class are equal. -/
theorem nat_squarefree_eq_of_mul_sq {a b A C : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hA : A ≠ 0) (hC : C ≠ 0) (h : a * A ^ 2 = b * C ^ 2) : a = b := by
  refine Nat.eq_of_factorization_eq ha.ne_zero hb.ne_zero fun p => ?_
  have h1 := congrArg (fun n => n.factorization p) h
  simp only [Nat.factorization_mul ha.ne_zero (pow_ne_zero 2 hA),
    Nat.factorization_mul hb.ne_zero (pow_ne_zero 2 hC), Nat.factorization_pow,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at h1
  have := ha.natFactorization_le_one p
  have := hb.natFactorization_le_one p
  omega

/-- Two squarefree integers in the same square class are equal. -/
theorem int_squarefree_eq_of_mul_sq {a b A C : ℤ} (ha : Squarefree a) (hb : Squarefree b)
    (hA : A ≠ 0) (hC : C ≠ 0) (h : a * A ^ 2 = b * C ^ 2) : a = b := by
  have habs : a.natAbs = b.natAbs := by
    refine nat_squarefree_eq_of_mul_sq (Int.squarefree_natAbs.mpr ha)
      (Int.squarefree_natAbs.mpr hb) (Int.natAbs_ne_zero.mpr hA) (Int.natAbs_ne_zero.mpr hC) ?_
    have := congrArg Int.natAbs h
    simpa [Int.natAbs_mul, Int.natAbs_pow] using this
  rcases Int.natAbs_eq_natAbs_iff.mp habs with h' | h'
  · exact h'
  · exfalso
    subst h'
    have hb0 : b ≠ 0 := hb.ne_zero
    have : b * (A ^ 2 + C ^ 2) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact hb0 h0
    · have : 0 < A ^ 2 + C ^ 2 := by positivity
      linarith

theorem sqfInt_spec {N : ℤ} (hN : N ≠ 0) :
    Squarefree (sqfInt N) ∧ ∃ c : ℤ, c ≠ 0 ∧ N = sqfInt N * c ^ 2 := by
  have hs : N.sign.natAbs = 1 := Int.natAbs_sign_of_ne_zero hN
  refine ⟨?_, ?_⟩
  · rw [← Int.squarefree_natAbs, sqfInt, Int.natAbs_mul, hs, one_mul, Int.natAbs_natCast]
    exact sqfNat_squarefree _
  · obtain ⟨k, hk, hk'⟩ := sqfNat_mul_sq (Int.natAbs_ne_zero.mpr hN)
    refine ⟨k, by exact_mod_cast hk, ?_⟩
    conv_lhs => rw [← Int.sign_mul_natAbs N, hk']
    push_cast [sqfInt]
    ring

theorem sqfInt_squarefree {N : ℤ} (hN : N ≠ 0) : Squarefree (sqfInt N) := (sqfInt_spec hN).1

/-- Uniqueness: if `N = d c²` with `d` squarefree, then `sqfInt N = d`. -/
theorem sqfInt_eq_of_eq_mul_sq {N d c : ℤ} (hd : Squarefree d) (hc : c ≠ 0)
    (h : N = d * c ^ 2) : sqfInt N = d := by
  have hN : N ≠ 0 := by rw [h]; exact mul_ne_zero hd.ne_zero (pow_ne_zero 2 hc)
  obtain ⟨hs, c', hc', h'⟩ := sqfInt_spec hN
  exact int_squarefree_eq_of_mul_sq hs hd hc' hc (h'.symm.trans h)

theorem sqfInt_mul_sq {N c : ℤ} (hN : N ≠ 0) (hc : c ≠ 0) : sqfInt (N * c ^ 2) = sqfInt N := by
  obtain ⟨hs, c', hc', h'⟩ := sqfInt_spec hN
  exact sqfInt_eq_of_eq_mul_sq hs (mul_ne_zero hc' hc) (by rw [mul_pow, ← mul_assoc, ← h'])

theorem sqf_intCast (N : ℤ) : sqf (N : ℚ) = sqfInt N := by
  simp [sqf]

theorem sqf_spec {x : ℚ} (hx : x ≠ 0) :
    Squarefree (sqf x) ∧ ∃ t : ℚ, t ≠ 0 ∧ x = sqf x * t ^ 2 := by
  have hN : x.num * (x.den : ℤ) ≠ 0 :=
    mul_ne_zero (Rat.num_ne_zero.mpr hx) (by exact_mod_cast x.den_ne_zero)
  obtain ⟨hs, c, hc, h⟩ := sqfInt_spec hN
  refine ⟨hs, (c : ℚ) / x.den, div_ne_zero (by exact_mod_cast hc) (by exact_mod_cast x.den_ne_zero),
    ?_⟩
  have hd : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_ne_zero
  have h' : (x.num : ℚ) * x.den = sqf x * c ^ 2 := by exact_mod_cast h
  rw [div_pow, mul_div_assoc', eq_div_iff (pow_ne_zero 2 hd), ← h', sq, ← mul_assoc,
    Rat.mul_den_eq_num]

theorem sqf_squarefree {x : ℚ} (hx : x ≠ 0) : Squarefree (sqf x) := (sqf_spec hx).1

/-- Uniqueness: if `x = d t²` with `d` squarefree and `t ≠ 0`, then `sqf x = d`. -/
theorem sqf_eq_of_eq_mul_sq {x t : ℚ} {d : ℤ} (hd : Squarefree d) (ht : t ≠ 0)
    (h : x = d * t ^ 2) : sqf x = d := by
  have hx : x ≠ 0 := by
    rw [h]; exact mul_ne_zero (by exact_mod_cast hd.ne_zero) (pow_ne_zero 2 ht)
  obtain ⟨hs, s, hs0, hs'⟩ := sqf_spec hx
  -- clear denominators: `sqf x · (s.num t.den)² = d · (t.num s.den)²`
  have hsn : s.num ≠ 0 := Rat.num_ne_zero.mpr hs0
  have htn : t.num ≠ 0 := Rat.num_ne_zero.mpr ht
  have key : ((sqf x * (s.num * t.den) ^ 2 : ℤ) : ℚ) = ((d * (t.num * s.den) ^ 2 : ℤ) : ℚ) := by
    have e1 : (s : ℚ) = s.num / s.den := (Rat.num_div_den s).symm
    have e2 : (t : ℚ) = t.num / t.den := (Rat.num_div_den t).symm
    have hsd : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_ne_zero
    have htd : (t.den : ℚ) ≠ 0 := by exact_mod_cast t.den_ne_zero
    rw [e1] at hs'; rw [e2] at h
    have := hs'.symm.trans h
    push_cast
    field_simp at this
    linear_combination this
  exact int_squarefree_eq_of_mul_sq hs hd (mul_ne_zero hsn (Int.natCast_ne_zero.mpr t.den_ne_zero))
    (mul_ne_zero htn (Int.natCast_ne_zero.mpr s.den_ne_zero)) (by exact_mod_cast key)

theorem sqf_mul_sq {x t : ℚ} (hx : x ≠ 0) (ht : t ≠ 0) : sqf (x * t ^ 2) = sqf x := by
  obtain ⟨hs, s, hs0, hs'⟩ := sqf_spec hx
  exact sqf_eq_of_eq_mul_sq hs (mul_ne_zero hs0 ht) (by rw [mul_pow, ← mul_assoc, ← hs'])

/-- The sign of `sqf x` is that of `x`. -/
theorem sqf_pos_iff {x : ℚ} (hx : x ≠ 0) : 0 < sqf x ↔ 0 < x := by
  obtain ⟨hs, t, ht, h⟩ := sqf_spec hx
  have ht2 : 0 < t ^ 2 := by positivity
  constructor
  · intro hpos; rw [h]; exact mul_pos (by exact_mod_cast hpos) ht2
  · intro hpos
    rw [h] at hpos
    exact_mod_cast pos_of_mul_pos_left hpos ht2.le

theorem Admissible.pos {B : ℚ} (hB : Admissible B) : 0 < B := hB.2.1

theorem Admissible.ne_zero {B : ℚ} (hB : Admissible B) : B ≠ 0 := hB.pos.ne'

/-- Integer form of `β` and `θ`: if `B = a/k²` in lowest terms, then `β = sqf(ma)` and
`θ = sqf((mk)² - ma)`. -/
theorem betaOf_thetaOf_eq_sqfInt {B : ℚ} {k : ℕ} (hk : B.den = k ^ 2) {m : ℤ} (hm : m ≠ 0)
    (hB : B ≠ 0) (hmB : (m : ℚ) ≠ B) :
    betaOf B m = sqfInt (m * B.num) ∧ thetaOf B m = sqfInt ((m * k) ^ 2 - m * B.num) := by
  have hk0 : (k : ℚ) ≠ 0 := by
    have := B.den_ne_zero; rw [hk] at this; exact_mod_cast pow_ne_zero_iff two_ne_zero |>.mp this
  have hBk : B = B.num / (k : ℚ) ^ 2 := by
    conv_lhs => rw [← Rat.num_div_den B]
    rw [hk]; push_cast; rfl
  have ha0 : B.num ≠ 0 := Rat.num_ne_zero.mpr hB
  obtain ⟨a, ha⟩ : ∃ a, B.num = a := ⟨_, rfl⟩
  rw [ha] at hBk ha0 ⊢
  have hk1 : (1 / (k : ℚ)) ≠ 0 := one_div_ne_zero hk0
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  constructor
  · rw [betaOf, show (m : ℚ) * B = ((m * a : ℤ) : ℚ) * (1 / k) ^ 2 by
      rw [hBk]; push_cast; field_simp, sqf_mul_sq (by exact_mod_cast mul_ne_zero hm ha0) hk1,
      sqf_intCast]
  · have hN : (m * k) ^ 2 - m * a ≠ 0 := by
      intro h0
      apply hmB
      have h1 : ((m * k : ℤ) : ℚ) ^ 2 - m * a = 0 := by exact_mod_cast h0
      rw [hBk]; field_simp; push_cast at h1
      apply mul_left_cancel₀ hm'
      linear_combination h1
    rw [thetaOf, show (m : ℚ) * (m - B) = (((m * k) ^ 2 - m * a : ℤ) : ℚ) * (1 / k) ^ 2 by
      rw [hBk]; push_cast; field_simp, sqf_mul_sq (by exact_mod_cast hN) hk1, sqf_intCast]

end ZInQ.RouteK
