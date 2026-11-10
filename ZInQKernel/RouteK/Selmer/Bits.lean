import ZInQKernel.RouteK.Selmer.BadOdd
import ZInQKernel.RouteK.Selmer.Real
import ZInQKernel.RouteK.Selmer.Two

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
  row `(D)`, `twoAdicRows 5` (`classCond_two_iff_D`). With Lemma T (`loc_two_adic_iff`,
  `Selmer/Two.lean`): `loc_two_selPair_iff`, `loc_two_selPair_iff_D`.
* `not_dvd_classInt`: at an odd prime `p ∤ d`, `a` and `b` are prime to `p`.
* `isSol_iff_selPair_mem_of_G2`: Proposition 0, first half, given Lemma G2 at the primes `p ∤ 2d`.

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

/-! ### Square classes of signed products at `2` -/

theorem oddClasses_pow {c : ZMod 8} (hc : c ∈ oddClasses) (n : ℕ) : c ^ n ∈ oddClasses := by
  induction n with
  | zero => rw [pow_zero]; decide
  | succ n ih => rw [pow_succ]; exact oddClasses_mul ih hc

theorem lam8_pow {c : ZMod 8} (hc : c ∈ oddClasses) (n : ℕ) : lam8 (c ^ n) = (n : ZMod 2) * lam8 c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, lam8_mul (oddClasses_pow hc n) hc, ih]; push_cast; ring

theorem mu8_pow {c : ZMod 8} (hc : c ∈ oddClasses) (n : ℕ) : mu8 (c ^ n) = (n : ZMod 2) * mu8 c := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mu8_mul (oddClasses_pow hc n) hc, ih]; push_cast; ring

theorem eq_one_iff_lam8_mu8 {c : ZMod 8} (hc : c ∈ oddClasses) : c = 1 ↔ lam8 c = 0 ∧ mu8 c = 0 := by
  revert c; decide

/-- An odd integer is a square in `ℚ₂` iff it is `≡ 1 (mod 8)`. -/
theorem isSquare_two_adic_intCast_iff {z : ℤ} (hz : Odd z) :
    IsSquare (z : ℚ_[2]) ↔ (z : ZMod 8) = 1 := by
  have hz2 : ¬((2 : ℕ) : ℤ) ∣ z := by
    rw [Nat.cast_ofNat, ← even_iff_two_dvd, Int.not_even_iff_odd]; exact hz
  have hu : ‖(z : ℤ_[2])‖ = 1 := by
    rw [PadicInt.norm_def, PadicInt.coe_intCast]; exact padic_norm_intCast_eq_one hz2
  have := isSquare_coe_iff_toZModPow_two hu
  rw [PadicInt.coe_intCast, map_intCast] at this
  exact this

theorem odd_prime_of_mem_primeFactors {d : ℕ} (hd : Odd d) (q : d.primeFactors) : (q : ℕ) % 2 = 1 :=
  Nat.odd_iff.mp ((prime_ne_two_of_mem_primeFactors hd q.2).1.odd_of_ne_two
    (prime_ne_two_of_mem_primeFactors hd q.2).2)

/-- The integer `(−1)^s 2^t Π_{q ∣ d} q^{e_q} 5^k` (`d` odd) is a square in `ℚ₂` iff `t` is even
and the odd part is `≡ 1 (mod 8)`, i.e. its characters `λ = s + Σ e_q λ_q` and
`μ = k + Σ e_q μ_q` vanish. -/
theorem isSquare_two_adic_signedProd_iff {d : ℕ} (hd : Odd d) (s t k : ℕ) (e : d.primeFactors → ℕ) :
    IsSquare (((((-1) ^ s * 2 ^ t * ∏ q : d.primeFactors, ((q : ℕ) : ℤ) ^ e q) * 5 ^ k : ℤ)) : ℚ_[2]) ↔
      Even t ∧ (s : ZMod 2) + ∑ q, (e q : ZMod 2) * lam8 ((q : ℕ) : ZMod 8) = 0 ∧
        (k : ZMod 2) + ∑ q, (e q : ZMod 2) * mu8 ((q : ℕ) : ZMod 8) = 0 := by
  set z : ℤ := (-1) ^ s * (∏ q : d.primeFactors, ((q : ℕ) : ℤ) ^ e q) * 5 ^ k
  have hN : ((-1) ^ s * 2 ^ t * ∏ q : d.primeFactors, ((q : ℕ) : ℤ) ^ e q) * 5 ^ k =
      ((2 : ℕ) : ℤ) ^ t * z := by
    simp only [z]; push_cast; ring
  have hodd : Odd z := by
    refine (odd_neg_one.pow.mul ?_).mul (by decide : Odd (5 : ℤ)).pow
    refine Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun q _ => Odd.pow ?_
    exact_mod_cast Nat.odd_iff.mpr (odd_prime_of_mem_primeFactors hd q)
  have hz2 : ¬((2 : ℕ) : ℤ) ∣ z := by
    rw [Nat.cast_ofNat, ← even_iff_two_dvd, Int.not_even_iff_odd]; exact hodd
  have hmem : ∀ q : d.primeFactors, ((q : ℕ) : ZMod 8) ∈ oddClasses := fun q =>
    natCast_mem_oddClasses (odd_prime_of_mem_primeFactors hd q)
  have hm1 : (-1 : ZMod 8) ∈ oddClasses := by decide
  have hm5 : (5 : ZMod 8) ∈ oddClasses := by decide
  have hP := prod_mem_oddClasses univ (fun q : d.primeFactors => ((q : ℕ) : ZMod 8) ^ e q)
    fun q _ => oddClasses_pow (hmem q) _
  have hcast : (z : ZMod 8) =
      (-1) ^ s * (∏ q : d.primeFactors, ((q : ℕ) : ZMod 8) ^ e q) * 5 ^ k := by
    simp only [z]; push_cast; rfl
  rw [hN, isSquare_padic_pow_mul_iff hz2, isSquare_two_adic_intCast_iff hodd, hcast,
    eq_one_iff_lam8_mu8 (oddClasses_mul (oddClasses_mul (oddClasses_pow hm1 s) hP)
      (oddClasses_pow hm5 k)),
    lam8_mul (oddClasses_mul (oddClasses_pow hm1 s) hP) (oddClasses_pow hm5 k),
    lam8_mul (oddClasses_pow hm1 s) hP, mu8_mul (oddClasses_mul (oddClasses_pow hm1 s) hP)
      (oddClasses_pow hm5 k), mu8_mul (oddClasses_pow hm1 s) hP, lam8_pow hm1, lam8_pow hm5,
    mu8_pow hm1, mu8_pow hm5, lam8_prod _ _ fun q _ => oddClasses_pow (hmem q) _,
    mu8_prod _ _ fun q _ => oddClasses_pow (hmem q) _]
  simp only [fun q => lam8_pow (hmem q), fun q => mu8_pow (hmem q),
    (by decide : lam8 (-1) = 1), (by decide : lam8 5 = 0), (by decide : mu8 (-1) = 0),
    (by decide : mu8 5 = 1), mul_one, mul_zero, add_zero, zero_add]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩; exact ⟨h₁, h₂, by rw [add_comm]; exact h₃⟩
  · rintro ⟨h₁, h₂, h₃⟩; exact ⟨h₁, h₂, by rw [add_comm]; exact h₃⟩

theorem natConfig_lam_eq_lam8 {d : ℕ} (hd : Odd d) (q : d.primeFactors) :
    (natConfig d hd).lam q = lam8 ((q : ℕ) : ZMod 8) := rfl

theorem natConfig_mu_eq_mu8 {d : ℕ} (hd : Odd d) (q : d.primeFactors) :
    (natConfig d hd).mu q = mu8 ((q : ℕ) : ZMod 8) := rfl

/-- For a squarefree `d`, the product of the classes mod 8 of its primes is `d mod 8`. -/
theorem prod_primeFactors_zmod8 {d : ℕ} (hd : Squarefree d) :
    ∏ q : d.primeFactors, ((q : ℕ) : ZMod 8) = (d : ZMod 8) := by
  rw [Finset.prod_coe_sort d.primeFactors (fun q : ℕ => (q : ZMod 8)), ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hd]

theorem natConfig_prodClass {d : ℕ} (hd : Odd d) (hsq : Squarefree d) :
    (natConfig d hd).prodClass = (d : ZMod 8) :=
  prod_primeFactors_zmod8 hsq

theorem bits_two_core (a0 a1 b0 b1 Lu Mu Lv Mv : ZMod 2) :
    (∃ x y z : ZMod 2, (a1 = 0 ∧ a0 + y + Lu = 0 ∧ Mu + x = 0) ∧
      (b1 = x ∧ b0 + y + Lv = 0 ∧ z + (Mv + y) = 0)) ↔
      a1 = 0 ∧ b1 = Mu ∧ a0 + Lu = b0 + Lv := by
  revert a0 a1 b0 b1 Lu Mu Lv Mv; decide

/-- **The place 2 in bits** (nt-prop0 §2.6, at `2`). Let `d ≡ 5 (mod 8)` be squarefree. The class
condition of Lemma T for `(a(σ), b(σ))` — `a d^i (−1)^j` and `b 2^i (−d)^j 5^k` are squares in
`ℚ₂` for some `i, j, k ∈ {0, 1}` — holds iff `a₁ = 0`, `b₁ = μ·u` and `a₀ + λ·u = b₀ + λ·v`. -/
theorem classCond_two_iff {d : ℕ} (hd5 : d % 8 = 5) (hsq : Squarefree d)
    (σ : Unknowns d.primeFactors) :
    (∃ i j k : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧
      IsSquare (((selPair d σ).1 * d ^ i * (-1) ^ j : ℤ) : ℚ_[2]) ∧
      IsSquare (((selPair d σ).2 * 2 ^ i * (-d) ^ j * 5 ^ k : ℤ) : ℚ_[2])) ↔
      σ.a1 = 0 ∧ σ.b1 = dot (natConfig d (odd_of_mod_eight_eq_five hd5)).mu σ.u ∧
        σ.a0 + dot (natConfig d (odd_of_mod_eight_eq_five hd5)).lam σ.u =
          σ.b0 + dot (natConfig d (odd_of_mod_eight_eq_five hd5)).lam σ.v := by
  set hd := odd_of_mod_eight_eq_five hd5
  have ha : ∀ i j : ℕ, (selPair d σ).1 * d ^ i * (-1) ^ j = ((-1) ^ (σ.a0.val + j) *
      2 ^ (σ.a1.val + 0) * ∏ q : d.primeFactors, ((q : ℕ) : ℤ) ^ ((σ.u q).val + i)) * 5 ^ 0 := by
    intro i j
    rw [← classInt_mul_eq hsq]
    simp only [selPair]; ring
  have hb : ∀ i j k : ℕ, (selPair d σ).2 * 2 ^ i * (-(d : ℤ)) ^ j * 5 ^ k = ((-1) ^ (σ.b0.val + j) *
      2 ^ (σ.b1.val + i) * ∏ q : d.primeFactors, ((q : ℕ) : ℤ) ^ ((σ.v q).val + j)) * 5 ^ k := by
    intro i j k
    rw [← classInt_mul_eq hsq]
    simp only [selPair]; rw [neg_pow]; ring
  have hd8 : (d : ZMod 8) = 5 := natCast_zmod8_of_mod hd5
  have hmem : ∀ q ∈ (univ : Finset d.primeFactors), ((q : ℕ) : ZMod 8) ∈ oddClasses := fun q _ =>
    natCast_mem_oddClasses (odd_prime_of_mem_primeFactors hd q)
  have hL : ∑ q : d.primeFactors, lam8 ((q : ℕ) : ZMod 8) = 0 := by
    rw [← lam8_prod _ _ hmem, prod_primeFactors_zmod8 hsq, hd8]; decide
  have hM : ∑ q : d.primeFactors, mu8 ((q : ℕ) : ZMod 8) = 1 := by
    rw [← mu8_prod _ _ hmem, prod_primeFactors_zmod8 hsq, hd8]; decide
  have hdotL : ∀ w : d.primeFactors → ZMod 2,
      dot (natConfig d hd).lam w = ∑ q, w q * lam8 ((q : ℕ) : ZMod 8) := fun w =>
    Finset.sum_congr rfl fun q _ => by rw [natConfig_lam_eq_lam8, mul_comm]
  have hdotM : ∀ w : d.primeFactors → ZMod 2,
      dot (natConfig d hd).mu w = ∑ q, w q * mu8 ((q : ℕ) : ZMod 8) := fun w =>
    Finset.sum_congr rfl fun q _ => by rw [natConfig_mu_eq_mu8, mul_comm]
  simp only [ha, hb]
  rw [bits_exists_three]
  simp only [isSquare_two_adic_signedProd_iff hd, bits_even_val_add_iff, bits_even_val_iff,
    Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_zero, add_zero, bits_sum_add_mul, hL, hM,
    mul_zero, mul_one, zero_add, hdotL, hdotM]
  exact bits_two_core _ _ _ _ _ _ _ _

/-- **Row `(D)`** (nt-prop0 §2.6, at `2`): under the sign row `(R)`, the class condition of
Lemma T for `(a(σ), b(σ))` is the row `(D)` of `Σ(𝒞_d)`, i.e. `twoAdicRows 5`. -/
theorem classCond_two_iff_D {d : ℕ} (hd5 : d % 8 = 5) (hsq : Squarefree d)
    (σ : Unknowns d.primeFactors) (hR : σ.a0 = σ.b0) :
    (∃ i j k : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧
      IsSquare (((selPair d σ).1 * d ^ i * (-1) ^ j : ℤ) : ℚ_[2]) ∧
      IsSquare (((selPair d σ).2 * 2 ^ i * (-d) ^ j * 5 ^ k : ℤ) : ℚ_[2])) ↔
      (natConfig d (odd_of_mod_eight_eq_five hd5)).D σ := by
  rw [classCond_two_iff hd5 hsq, Config.D, natConfig_prodClass _ hsq,
    natCast_zmod8_of_mod hd5, Nat.cast_ofNat, Config.twoAdicRows_five, hR, add_right_inj]
  exact and_congr_right fun _ => and_congr_right fun _ => eq_comm

/-- The rows `(R)` and `(D)` together are the class conditions at `∞` and at `2`. -/
theorem classCond_two_and_R_iff {d : ℕ} (hd5 : d % 8 = 5) (hsq : Squarefree d)
    (σ : Unknowns d.primeFactors) :
    ((∃ i j k : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧
      IsSquare (((selPair d σ).1 * d ^ i * (-1) ^ j : ℤ) : ℚ_[2]) ∧
      IsSquare (((selPair d σ).2 * 2 ^ i * (-d) ^ j * 5 ^ k : ℤ) : ℚ_[2])) ∧ σ.a0 = σ.b0) ↔
      (natConfig d (odd_of_mod_eight_eq_five hd5)).D σ ∧ σ.a0 = σ.b0 :=
  ⟨fun ⟨h, hR⟩ => ⟨(classCond_two_iff_D hd5 hsq σ hR).mp h, hR⟩,
    fun ⟨h, hR⟩ => ⟨(classCond_two_iff_D hd5 hsq σ hR).mpr h, hR⟩⟩

/-- **Lemma T in bits** (nt-prop0 §2.6, at `2`): for squarefree `d ≡ 5 (mod 8)`, the covering of
`(a(σ), b(σ))` is soluble over `ℚ₂` iff `a₁ = 0`, `b₁ = μ·u` and `a₀ + λ·u = b₀ + λ·v`. -/
theorem loc_two_selPair_iff {d : ℕ} (hd5 : d % 8 = 5) (hsq : Squarefree d)
    (σ : Unknowns d.primeFactors) :
    Loc ℚ_[2] d (selPair d σ).1 (selPair d σ).2 ↔
      σ.a1 = 0 ∧ σ.b1 = dot (natConfig d (odd_of_mod_eight_eq_five hd5)).mu σ.u ∧
        σ.a0 + dot (natConfig d (odd_of_mod_eight_eq_five hd5)).lam σ.u =
          σ.b0 + dot (natConfig d (odd_of_mod_eight_eq_five hd5)).lam σ.v := by
  rw [loc_two_adic_iff hd5 (selPair d σ).1 (selPair d σ).2 (classInt_ne_zero _ _ _ _)
    (classInt_ne_zero _ _ _ _)]
  exact classCond_two_iff hd5 hsq σ

/-- **Row `(D)` from Lemma T** (nt-prop0 §2.6): under `(R)`, the covering of `(a(σ), b(σ))` is
soluble over `ℚ₂` iff `σ` satisfies the row `(D)` (`twoAdicRows 5`). -/
theorem loc_two_selPair_iff_D {d : ℕ} (hd5 : d % 8 = 5) (hsq : Squarefree d)
    (σ : Unknowns d.primeFactors) (hR : σ.a0 = σ.b0) :
    Loc ℚ_[2] d (selPair d σ).1 (selPair d σ).2 ↔
      (natConfig d (odd_of_mod_eight_eq_five hd5)).D σ := by
  rw [loc_two_adic_iff hd5 (selPair d σ).1 (selPair d σ).2 (classInt_ne_zero _ _ _ _)
    (classInt_ne_zero _ _ _ _)]
  exact classCond_two_iff_D hd5 hsq σ hR

/-! ### The real place -/

/-- **Row `(R)`** (nt-prop0 §2.6, at `∞`): the covering of `(a(σ), b(σ))` is soluble over `ℝ` iff
`a₀ = b₀`. -/
theorem loc_real_selPair_iff {d : ℕ} (hd0 : d ≠ 0) (σ : Unknowns d.primeFactors) :
    Loc ℝ d (selPair d σ).1 (selPair d σ).2 ↔ σ.a0 = σ.b0 := by
  rw [show selPair d σ = (classInt d σ.a0 σ.a1 σ.u, classInt d σ.b0 σ.b1 σ.v) from rfl,
    loc_real_iff_int hd0 (classInt_ne_zero _ _ _ _) (classInt_ne_zero _ _ _ _)]
  rw [classInt_pos_iff, classInt_pos_iff]
  rcases zmod2_cases σ.a0 with h | h <;> rcases zmod2_cases σ.b0 with h' | h' <;> simp [h, h']

/-! ### Squarefreeness -/

/-- `classInt d e₀ e₁ w = (−1)^{e₀} 2^{e₁} Π_{q ∣ d} q^{w_q}` is squarefree for odd `d`, so
`a(σ)` and `b(σ)` are squarefree (nt-prop0 §2.7, proof of Proposition 0). -/
theorem squarefree_classInt {d : ℕ} (hd : Odd d) (e₀ e₁ : ZMod 2) (w : d.primeFactors → ZMod 2) :
    Squarefree (classInt d e₀ e₁ w) := by
  have hpow : ∀ n : ℕ, n.Prime → ∀ e : ZMod 2, Squarefree (n ^ e.val) := fun n hn e => by
    rcases zmod2_cases e with rfl | rfl
    · simp
    · rw [show (1 : ZMod 2).val = 1 from rfl, pow_one]; exact hn.squarefree
  rw [← Int.squarefree_natAbs]
  have habs : (classInt d e₀ e₁ w).natAbs = 2 ^ e₁.val * ∏ q : d.primeFactors, (q : ℕ) ^ (w q).val := by
    have : classInt d e₀ e₁ w =
        (-1) ^ e₀.val * ((2 ^ e₁.val * ∏ q : d.primeFactors, (q : ℕ) ^ (w q).val : ℕ) : ℤ) := by
      unfold classInt; push_cast; ring
    rw [this, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    simp
  rw [habs, Nat.squarefree_mul_iff]
  refine ⟨?_, hpow 2 Nat.prime_two _, ?_⟩
  · refine Nat.Coprime.prod_right fun q _ => Nat.Coprime.pow _ _ ?_
    obtain ⟨hq, hq2⟩ := prime_ne_two_of_mem_primeFactors hd q.2
    exact (Nat.coprime_primes Nat.prime_two hq).mpr (Ne.symm hq2)
  · refine Finset.squarefree_prod_of_pairwise_isCoprime (fun a _ b _ hab => ?_)
      fun q _ => hpow q (Nat.prime_of_mem_primeFactors q.2) _
    simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors a.2)
      (Nat.prime_of_mem_primeFactors b.2)).mpr fun h => hab (Subtype.ext h))

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

/-! ### Assembly, given Lemmas T and G2 -/

/-- **Proposition 0, first half, from the local lemmas** (nt-prop0 §2.7). Let `d ≡ 5 (mod 8)` be
squarefree. Given Lemma T at 2 (`hT`, the statement of §2.5) and Lemma G2 at the primes `p ∤ 2d`
(`hG`), `σ` solves `Σ(𝒞_d)` iff `(a(σ), b(σ)) ∈ Sel₂(C_d)`. -/
theorem isSol_iff_selPair_mem_of_local {d : ℕ} (hd5 : d % 8 = 5) (hsq : Squarefree d)
    (hT : ∀ a b : ℤ, a ≠ 0 → b ≠ 0 → (Loc ℚ_[2] d a b ↔ ∃ i j k : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧
      IsSquare ((a * d ^ i * (-1) ^ j : ℤ) : ℚ_[2]) ∧
      IsSquare ((b * 2 ^ i * (-d) ^ j * 5 ^ k : ℤ) : ℚ_[2])))
    (hG : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬p ∣ d → ∀ a b : ℤ, ¬(p : ℤ) ∣ a → ¬(p : ℤ) ∣ b →
      Loc ℚ_[p] d a b)
    (σ : Unknowns d.primeFactors) :
    (natConfig d (odd_of_mod_eight_eq_five hd5)).IsSol σ ↔ selPair d σ ∈ Sel2 d := by
  set hd := odd_of_mod_eight_eq_five hd5
  have hd0 : d ≠ 0 := by omega
  have ha0 : (selPair d σ).1 ≠ 0 := classInt_ne_zero _ _ _ _
  have hb0 : (selPair d σ).2 ≠ 0 := classInt_ne_zero _ _ _ _
  constructor
  · rintro ⟨hE1, hE2, hR, hD⟩
    refine ⟨squarefree_classInt hd _ _ _, squarefree_classInt hd _ _ _,
      (loc_real_selPair_iff hd0 σ).mpr hR, fun p _ => ?_⟩
    by_cases hp2 : p = 2
    · subst hp2
      exact (hT _ _ ha0 hb0).mpr ((classCond_two_iff_D hd5 hsq σ hR).mpr hD)
    by_cases hpd : p ∣ d
    · have hmem : p ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨Fact.out, hpd, hd0⟩
      exact (loc_padic_selPair_iff_rows hd hsq σ hmem).mpr ⟨hE1 _, hE2 _⟩
    · exact hG p hp2 hpd _ _ (not_dvd_selPair Fact.out hp2 hpd σ).1
        (not_dvd_selPair Fact.out hp2 hpd σ).2
  · rintro ⟨-, -, hR, hloc⟩
    have hR' := (loc_real_selPair_iff hd0 σ).mp hR
    have hrows : ∀ x : d.primeFactors,
        (natConfig d hd).E1 σ x ∧ (natConfig d hd).E2 σ x := fun x => by
      have : Fact (x : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors x.2⟩
      exact (loc_padic_selPair_iff_rows hd hsq σ x.2).mp (hloc x)
    exact ⟨fun x => (hrows x).1, fun x => (hrows x).2, hR',
      (classCond_two_iff_D hd5 hsq σ hR').mp ((hT _ _ ha0 hb0).mp (hloc 2))⟩

/-- **Proposition 0, first half, from Lemma G2** (nt-prop0 §2.7): with Lemma T proved
(`loc_two_adic_iff`), only Lemma G2 at the primes `p ∤ 2d` remains as a hypothesis. -/
theorem isSol_iff_selPair_mem_of_G2 {d : ℕ} (hd5 : d % 8 = 5) (hsq : Squarefree d)
    (hG : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬p ∣ d → ∀ a b : ℤ, ¬(p : ℤ) ∣ a → ¬(p : ℤ) ∣ b →
      Loc ℚ_[p] d a b)
    (σ : Unknowns d.primeFactors) :
    (natConfig d (odd_of_mod_eight_eq_five hd5)).IsSol σ ↔ selPair d σ ∈ Sel2 d :=
  isSol_iff_selPair_mem_of_local hd5 hsq (fun a b ha hb => loc_two_adic_iff hd5 a b ha hb) hG σ

end ZInQ.RouteK.Selmer
