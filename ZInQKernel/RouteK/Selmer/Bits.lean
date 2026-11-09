import ZInQKernel.RouteK.Selmer.BadOdd
import ZInQKernel.RouteK.Selmer.Real

/-!
# From local classes to the rows of `Σ(𝒞_d)`

`docs/research/nt-prop0.md` §2.6. For unknowns `σ` of the Selmer system on the prime factors of a
squarefree odd `d`, let `a = a(σ)` and `b = b(σ)` be the integers `classInt …` of `selPair d σ`.
This file turns the local class conditions of Lemmas B, ∞ and T into the rows of `Σ(𝒞_d)`
(`natConfig d`):

* `classCond_dvd_iff_rows`: at an odd prime `p ∣ d`, the right-hand side of `loc_padic_dvd_iff`
  for `(a, b)` is equivalent to `E1_p ∧ E2_p`; with Lemma B, `loc_padic_selPair_iff_rows`.
* `loc_real_selPair_iff`: at `∞`, `Loc ℝ d a b` is the sign row `(R)`, `a₀ = b₀`.
* `classCond_two_iff`: at `2`, for `d ≡ 5 (mod 8)`, the class condition of Lemma T
  (`a d^i (−1)^j` and `b 2^i (−d)^j 5^k` squares in `ℚ₂` for some `i, j, k ∈ {0, 1}`) is
  equivalent to `a₁ = 0`, `b₁ = μ·u` and `a₀ + λ·u = b₀ + λ·v`; together with `(R)` this is the
  row `(D)`, `twoAdicRows 5` (`classCond_two_iff_D`).
* `not_dvd_classInt`: at an odd prime `p ∤ d`, `a` and `b` are prime to `p`.

The common step writes `a d^i (−1)^j` and `b 2^i (−d)^j` as `(−1)^s 2^t Π_{q ∣ d} q^{e_q}`
(`classInt_mul_eq`, using `d = Π_{q ∣ d} q`) and reads the square class off the exponents:
the `p`-adic valuation `e_p` and the residue bit `s λ_p + t μ_p + Σ_{q ≠ p} e_q [q/p]`
(`isSquare_padic_signedProd_iff`, through `legBit` multiplicativity), resp. at `2` the exponent
`t` and the mod-8 characters `lam8`, `mu8` of the odd part (`isSquare_two_adic_signedProd_iff`).
-/

namespace ZInQ.RouteK.Selmer

open Finset

/-! ### Bits and exponents -/

theorem bits_exists_two {Q : ℕ → ℕ → Prop} :
    (∃ i j : ℕ, i < 2 ∧ j < 2 ∧ Q i j) ↔ ∃ x y : ZMod 2, Q x.val y.val := by
  constructor
  · rintro ⟨i, j, hi, hj, h⟩
    refine ⟨i, j, ?_⟩
    rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]
  · rintro ⟨x, y, h⟩
    exact ⟨_, _, x.val_lt, y.val_lt, h⟩

theorem bits_exists_three {Q : ℕ → ℕ → ℕ → Prop} :
    (∃ i j k : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧ Q i j k) ↔ ∃ x y z : ZMod 2, Q x.val y.val z.val := by
  constructor
  · rintro ⟨i, j, k, hi, hj, hk, h⟩
    refine ⟨i, j, k, ?_⟩
    rwa [ZMod.val_natCast, ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hi,
      Nat.mod_eq_of_lt hj, Nat.mod_eq_of_lt hk]
  · rintro ⟨x, y, z, h⟩
    exact ⟨_, _, _, x.val_lt, y.val_lt, z.val_lt, h⟩

theorem bits_even_val_add_iff (a b : ZMod 2) : Even (a.val + b.val) ↔ a = b := by
  revert a b; decide

theorem bits_even_val_iff (a : ZMod 2) : Even a.val ↔ a = 0 := by
  revert a; decide

/-- A squarefree `d` is the product of its prime factors, as an integer. -/
theorem intCast_eq_prod_primeFactors {d : ℕ} (hd : Squarefree d) :
    (d : ℤ) = ∏ q : d.primeFactors, ((q : ℕ) : ℤ) := by
  rw [Finset.prod_coe_sort d.primeFactors (fun q : ℕ => (q : ℤ)), ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hd]

/-- `a(σ) (−1)^s 2^t d^m = (−1)^{a₀ + s} 2^{a₁ + t} Π_{q ∣ d} q^{u_q + m}`. -/
theorem classInt_mul_eq {d : ℕ} (hd : Squarefree d) (e₀ e₁ : ZMod 2) (w : d.primeFactors → ZMod 2)
    (s t m : ℕ) :
    classInt d e₀ e₁ w * (-1) ^ s * 2 ^ t * (d : ℤ) ^ m =
      (-1) ^ (e₀.val + s) * 2 ^ (e₁.val + t) * ∏ q : d.primeFactors, ((q : ℕ) : ℤ) ^ ((w q).val + m) := by
  rw [intCast_eq_prod_primeFactors hd, ← Finset.prod_pow]
  simp only [classInt, pow_add, Finset.prod_mul_distrib]
  ring

/-! ### Square classes of signed products at an odd prime `p ∣ d` -/

section Odd

variable {p : ℕ} [hp : Fact p.Prime]

/-- An integer `p^e z` with `p ∤ z` is a square in `ℚ_p` iff `e` is even and `z` is a square. -/
theorem isSquare_padic_pow_mul_iff {z : ℤ} (hz : ¬(p : ℤ) ∣ z) (e : ℕ) :
    IsSquare ((((p : ℤ) ^ e * z : ℤ)) : ℚ_[p]) ↔ Even e ∧ IsSquare (z : ℚ_[p]) := by
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hz1 := padic_norm_intCast_eq_one hz
  push_cast
  rcases Nat.even_or_odd e with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · rw [show (p : ℚ_[p]) ^ (m + m) * (z : ℚ_[p]) = (z : ℚ_[p]) * ((p : ℚ_[p]) ^ m) ^ 2 by ring,
      isSquare_mul_sq_iff (pow_ne_zero _ hp0)]
    exact ⟨fun h => ⟨⟨m, rfl⟩, h⟩, fun h => h.2⟩
  · refine iff_of_false (fun h => ?_) (fun h => (Nat.not_even_iff_odd.mpr ⟨m, rfl⟩) h.1)
    have hz0 : (z : ℚ_[p]) ≠ 0 := by intro h0; rw [h0, norm_zero] at hz1; exact zero_ne_one hz1
    refine padic_norm_ne_zpow_odd (mul_ne_zero (pow_ne_zero _ hp0) hz0) h (-(m : ℤ) - 1) ?_
    rw [norm_mul, norm_pow, Padic.norm_p, hz1, mul_one, inv_pow, ← zpow_natCast, ← zpow_neg]
    congr 1
    push_cast; ring

theorem legBit_pow {z : ℤ} (hz : (z : ZMod p) ≠ 0) (n : ℕ) :
    legBit p (z ^ n) = (n : ZMod 2) * legBit p z := by
  induction n with
  | zero => simp [legBit, IsSquare.one]
  | succ n ih =>
    rw [pow_succ, legBit_mul (by push_cast; exact pow_ne_zero _ hz) hz, ih]
    push_cast; ring

theorem bits_neg_one_ne_zero : (((-1 : ℤ)) : ZMod p) ≠ 0 := by
  push_cast; exact neg_ne_zero.mpr one_ne_zero

theorem bits_two_ne_zero (hp2 : p ≠ 2) : (((2 : ℤ)) : ZMod p) ≠ 0 := by
  have := natCast_zmod_ne_zero_of_prime_ne hp.out Nat.prime_two hp2
  exact_mod_cast this

/-- For an odd prime `p ∣ d`, the integer `(−1)^s 2^t Π_{q ∣ d} q^{e_q}` is a square in `ℚ_p` iff
`e_p` is even and its residue bit `s λ_p + t μ_p + Σ_{q ≠ p} e_q [q/p]` vanishes. -/
theorem isSquare_padic_signedProd_iff {d : ℕ} (hd : Odd d) (hpd : p ∈ d.primeFactors)
    (s t : ℕ) (e : d.primeFactors → ℕ) :
    IsSquare ((((-1) ^ s * 2 ^ t * ∏ q : d.primeFactors, ((q : ℕ) : ℤ) ^ e q : ℤ)) : ℚ_[p]) ↔
      Even (e ⟨p, hpd⟩) ∧ (s : ZMod 2) * lamBit p + (t : ZMod 2) * muBit p +
        ∑ q ∈ univ.erase ⟨p, hpd⟩, (e q : ZMod 2) * legBit p (q : ℕ) = 0 := by
  set q₀ : d.primeFactors := ⟨p, hpd⟩
  have hp2 : p ≠ 2 := (prime_ne_two_of_mem_primeFactors hd hpd).2
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hne : ∀ q ∈ univ.erase q₀, (((q : ℕ) : ℤ) : ZMod p) ≠ 0 := fun q hq =>
    natCast_zmod_ne_zero_of_prime_ne hp.out (Nat.prime_of_mem_primeFactors q.2)
      fun h => (Finset.ne_of_mem_erase hq) (Subtype.ext h.symm)
  set P := ∏ q ∈ univ.erase q₀, ((q : ℕ) : ℤ) ^ e q
  have hsplit : (-1) ^ s * 2 ^ t * ∏ q : d.primeFactors, ((q : ℕ) : ℤ) ^ e q =
      (p : ℤ) ^ e q₀ * ((-1) ^ s * 2 ^ t * P) := by
    rw [← Finset.mul_prod_erase univ _ (mem_univ q₀)]; ring
  have hP : ((P : ℤ) : ZMod p) ≠ 0 := by
    simp only [P, Int.cast_prod, Int.cast_pow]
    exact Finset.prod_ne_zero_iff.mpr fun q hq => pow_ne_zero _ (by exact_mod_cast hne q hq)
  have hz : (((-1) ^ s * 2 ^ t * P : ℤ) : ZMod p) ≠ 0 := by
    have h1 := bits_neg_one_ne_zero (p := p)
    have h2 := bits_two_ne_zero (p := p) hp2
    push_cast at h1 h2 hP ⊢
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h2)) hP
  have hz' : ¬(p : ℤ) ∣ (-1) ^ s * 2 ^ t * P := fun h =>
    hz ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h)
  rw [hsplit, isSquare_padic_pow_mul_iff hz']
  have hsq : IsSquare ((((-1) ^ s * 2 ^ t * P : ℤ)) : ℚ_[p]) ↔
      legBit p ((-1) ^ s * 2 ^ t * P) = 0 := by
    have hu : ‖((((-1) ^ s * 2 ^ t * P : ℤ)) : ℤ_[p])‖ = 1 := by
      rw [PadicInt.norm_def, PadicInt.coe_intCast]; exact padic_norm_intCast_eq_one hz'
    have := isSquare_coe_iff_toZMod hp2 hu
    rw [PadicInt.coe_intCast, map_intCast] at this
    rw [this, legBit]
    exact ⟨fun h' => ite_eq_left h', fun h' => by_contra fun hn => by
      rw [ite_eq_right hn] at h'; exact one_ne_zero h'⟩
  rw [hsq]
  have h1 := bits_neg_one_ne_zero (p := p)
  have h2 := bits_two_ne_zero (p := p) hp2
  rw [legBit_mul (by push_cast at h1 h2 ⊢; exact mul_ne_zero (pow_ne_zero _ h1) (pow_ne_zero _ h2))
      hP, legBit_mul (by push_cast at h1 ⊢; exact pow_ne_zero _ h1)
      (by push_cast at h2 ⊢; exact pow_ne_zero _ h2), legBit_pow h1, legBit_pow h2,
    legBit_prod _ _ fun q hq => by push_cast; exact pow_ne_zero _ (by exact_mod_cast hne q hq)]
  rw [Finset.sum_congr rfl fun q hq => legBit_pow (hne q hq) (e q)]
  rfl

/-- `μ` of the class mod 8 of an odd prime is `μ_p = [2/p]`. -/
theorem mu8_natCast_eq_muBit_of_prime {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    mu8 (q : ZMod 8) = muBit q := by
  have := Fact.mk hq
  rw [muBit_eq q hq2]
  have hodd : q % 2 = 1 := (hq.eq_two_or_odd).resolve_left hq2
  have h : q % 8 = 1 ∨ q % 8 = 3 ∨ q % 8 = 5 ∨ q % 8 = 7 := by omega
  rcases h with h | h | h | h <;> rw [natCast_zmod8_of_mod h, h] <;> decide

theorem natConfig_lam {d : ℕ} (hd : Odd d) (q : d.primeFactors) :
    (natConfig d hd).lam q = lamBit q :=
  primeCfg_lam _ _ _ q

theorem natConfig_mu {d : ℕ} (hd : Odd d) (q : d.primeFactors) :
    (natConfig d hd).mu q = muBit q :=
  mu8_natCast_eq_muBit_of_prime (prime_ne_two_of_mem_primeFactors hd q.2).1
    (prime_ne_two_of_mem_primeFactors hd q.2).2

theorem natConfig_bit {d : ℕ} (hd : Odd d) (y x : d.primeFactors) :
    (natConfig d hd).bit y x = legBit x y := rfl

theorem bits_eq_iff_add_eq_zero (x y : ZMod 2) : x = y ↔ x + y = 0 := by
  revert x y; decide

theorem bits_exists_eq_and_eq {u₀ v₀ : ZMod 2} {P Q : ZMod 2 → ZMod 2 → Prop} :
    (∃ x y : ZMod 2, (u₀ = x ∧ P x y) ∧ (v₀ = y ∧ Q x y)) ↔ P u₀ v₀ ∧ Q u₀ v₀ :=
  ⟨fun ⟨_, _, ⟨hx, h₁⟩, ⟨hy, h₂⟩⟩ => by subst hx hy; exact ⟨h₁, h₂⟩,
    fun ⟨h₁, h₂⟩ => ⟨u₀, v₀, ⟨rfl, h₁⟩, ⟨rfl, h₂⟩⟩⟩

theorem bits_sum_add_mul {κ : Type*} (s : Finset κ) (w L : κ → ZMod 2) (x : ZMod 2) :
    ∑ q ∈ s, (w q + x) * L q = ∑ q ∈ s, w q * L q + x * ∑ q ∈ s, L q := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **Rows `E1_p`, `E2_p`** (nt-prop0 §2.6, at `p ∈ S`). For an odd prime `p ∣ d`, the class
condition of Lemma B (`loc_padic_dvd_iff`) for `(a(σ), b(σ))` is equivalent to the rows `E1_p` and
`E2_p` of `Σ(𝒞_d)`. -/
theorem classCond_dvd_iff_rows {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (σ : Unknowns d.primeFactors) (hpd : p ∈ d.primeFactors) :
    (∃ i j : ℕ, i < 2 ∧ j < 2 ∧
      IsSquare (((selPair d σ).1 * d ^ i * (-1) ^ j : ℤ) : ℚ_[p]) ∧
      IsSquare (((selPair d σ).2 * 2 ^ i * (-d) ^ j : ℤ) : ℚ_[p])) ↔
      (natConfig d hd).E1 σ ⟨p, hpd⟩ ∧ (natConfig d hd).E2 σ ⟨p, hpd⟩ := by
  set q₀ : d.primeFactors := ⟨p, hpd⟩
  have ha : ∀ i j : ℕ, (selPair d σ).1 * d ^ i * (-1) ^ j = (-1) ^ (σ.a0.val + j) *
      2 ^ (σ.a1.val + 0) * ∏ q : d.primeFactors, ((q : ℕ) : ℤ) ^ ((σ.u q).val + i) := by
    intro i j
    rw [← classInt_mul_eq hsq]
    simp only [selPair]; ring
  have hb : ∀ i j : ℕ, (selPair d σ).2 * 2 ^ i * (-(d : ℤ)) ^ j = (-1) ^ (σ.b0.val + j) *
      2 ^ (σ.b1.val + i) * ∏ q : d.primeFactors, ((q : ℕ) : ℤ) ^ ((σ.v q).val + j) := by
    intro i j
    rw [← classInt_mul_eq hsq]
    simp only [selPair]; rw [neg_pow]; ring
  have hK : ∀ w : d.primeFactors → ZMod 2, (natConfig d hd).monsky w q₀ =
      ∑ q ∈ univ.erase q₀, w q * legBit p (q : ℕ) + w q₀ * ∑ q ∈ univ.erase q₀, legBit p (q : ℕ) := by
    intro w
    rw [← bits_sum_add_mul]
    exact Finset.sum_congr rfl fun q _ => by rw [natConfig_bit]; ring
  simp only [ha, hb]
  rw [bits_exists_two]
  simp only [isSquare_padic_signedProd_iff hd hpd, bits_even_val_add_iff, Nat.cast_add,
    ZMod.natCast_zmod_val, Nat.cast_zero, bits_sum_add_mul]
  rw [bits_exists_eq_and_eq]
  simp only [Config.E1, Config.E2, hK, natConfig_lam, natConfig_mu]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨(bits_eq_iff_add_eq_zero _ _).mpr (by linear_combination h₁),
      (bits_eq_iff_add_eq_zero _ _).mpr (by linear_combination h₂)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨by linear_combination (bits_eq_iff_add_eq_zero _ _).mp h₁,
      by linear_combination (bits_eq_iff_add_eq_zero _ _).mp h₂⟩

theorem classInt_ne_zero (d : ℕ) (e₀ e₁ : ZMod 2) (w : d.primeFactors → ZMod 2) :
    classInt d e₀ e₁ w ≠ 0 := by
  unfold classInt
  exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num)))
    (classInt_prod_pos d w).ne'

/-- **Lemma B in bits** (nt-prop0 §2.6): for an odd prime `p ∣ d`, the covering of
`(a(σ), b(σ))` is soluble over `ℚ_p` iff `σ` satisfies the rows `E1_p` and `E2_p`. -/
theorem loc_padic_selPair_iff_rows {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (σ : Unknowns d.primeFactors) (hpd : p ∈ d.primeFactors) :
    Loc ℚ_[p] d (selPair d σ).1 (selPair d σ).2 ↔
      (natConfig d hd).E1 σ ⟨p, hpd⟩ ∧ (natConfig d hd).E2 σ ⟨p, hpd⟩ := by
  rw [show selPair d σ = (classInt d σ.a0 σ.a1 σ.u, classInt d σ.b0 σ.b1 σ.v) from rfl,
    loc_padic_dvd_iff (prime_ne_two_of_mem_primeFactors hd hpd).2
    (Nat.dvd_of_mem_primeFactors hpd) hsq _ _ (classInt_ne_zero _ _ _ _)
    (classInt_ne_zero _ _ _ _)]
  exact classCond_dvd_iff_rows hd hsq σ hpd

end Odd

/-! ### The real place -/

/-- **Row `(R)`** (nt-prop0 §2.6, at `∞`): the covering of `(a(σ), b(σ))` is soluble over `ℝ` iff
`a₀ = b₀`. -/
theorem loc_real_selPair_iff {d : ℕ} (hd0 : d ≠ 0) (σ : Unknowns d.primeFactors) :
    Loc ℝ d (selPair d σ).1 (selPair d σ).2 ↔ σ.a0 = σ.b0 := by
  rw [show selPair d σ = (classInt d σ.a0 σ.a1 σ.u, classInt d σ.b0 σ.b1 σ.v) from rfl,
    loc_real_iff_int hd0 (classInt_ne_zero _ _ _ _) (classInt_ne_zero _ _ _ _)]
  rw [classInt_pos_iff, classInt_pos_iff]
  rcases zmod2_cases σ.a0 with h | h <;> rcases zmod2_cases σ.b0 with h' | h' <;> simp [h, h']

/-! ### Good primes -/

/-- At an odd prime `p ∤ d`, `classInt d e₀ e₁ w = (−1)^{e₀} 2^{e₁} Π_{q ∣ d} q^{w_q}` is prime to
`p` (nt-prop0 §2.6, at `p ∉ S ∪ {2}`). -/
theorem not_dvd_classInt {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬p ∣ d) (e₀ e₁ : ZMod 2)
    (w : d.primeFactors → ZMod 2) : ¬(p : ℤ) ∣ classInt d e₀ e₁ w := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  unfold classInt
  rw [hpZ.dvd_mul, hpZ.dvd_mul, hpZ.dvd_finsetProd_iff]
  rintro ((h | h) | ⟨q, -, h⟩)
  · exact hpZ.not_isUnit (isUnit_of_dvd_unit h ((isUnit_neg_one).pow _))
  · have : p ∣ 2 := by exact_mod_cast hpZ.dvd_of_dvd_pow h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  · have : p ∣ (q : ℕ) := by exact_mod_cast hpZ.dvd_of_dvd_pow h
    exact hpd (this.trans (Nat.dvd_of_mem_primeFactors q.2))

/-- At an odd prime `p ∤ d`, both `a(σ)` and `b(σ)` are prime to `p`. -/
theorem not_dvd_selPair {d p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬p ∣ d)
    (σ : Unknowns d.primeFactors) :
    ¬(p : ℤ) ∣ (selPair d σ).1 ∧ ¬(p : ℤ) ∣ (selPair d σ).2 :=
  ⟨not_dvd_classInt hp hp2 hpd _ _ _, not_dvd_classInt hp hp2 hpd _ _ _⟩

end ZInQ.RouteK.Selmer
