import Mathlib

/-!
# Lane RC23-visibility: the explicit Hilbert symbols of the extracted character

Manuscript, Appendix F, proof of Proposition `ex:app-theta-form` (tex 8409–9099): the determinant
factor of the extracted form and the characters (O.5) (tex 8888–8924), with the extraction paragraphs
(tex 8968–8988 and 9019–9036).

For the extracted form `Q_B' = Q_B/m`, `m = |h_*|` odd with `m ≡ 3 (mod 4)`, the determinant
squareclass is `m^{-3} ≡ m` (tex 8888–8890, 8974–8975, 9033–9034), so the local operator character
acquires the factor `u ↦ (u, m)_p`. This file writes the Hilbert symbols by Serre's explicit
formulas (`hilbertOdd`, `hilbertTwo`, `hilbertInf`) and proves, for these formulas:

* `(u, m)_p = (u/p)^{v_p(m)}` for a unit `u` at an odd prime `p` (tex 8893–8894): `hilbertOdd_unit`;
* `(u, m)_2 = (−1)^{((u−1)/2)((m−1)/2)}` for odd `u, m` (tex 8894–8895): `hilbertTwo_odd_odd`,
  `hilbertTwo_odd_odd'`;
* for `m ≡ 3 (mod 4)` this is `(−1)^{(u−1)/2}`, trivial on `1 + 4ℤ₂` (tex 8896–8898):
  `hilbertTwo_of_three_mod_four`, `hilbertTwo_of_three_mod_four'`, `hilbertTwo_of_one_mod_four`;
* the symbol at a prime dividing neither entry is one (tex 8899, 8912–8913): `hilbertOdd_of_not_dvd`;
  at an odd `q ∣ d` it is `(m/q)^{v_q(d)}` (tex 8913–8914): `hilbertOdd_at_divisor`;
* (O.5c): `∏_{p ∣ 2m} (d, m)_p = ∏_{q ∣ d} (m/q)^{v_q(d)} = (m/d)` for odd coprime `d, m > 0`
  (tex 8907–8915): `O5c`, `O5c'`, `O5c_divisor_side`; and Hilbert reciprocity in this case,
  `hilbert_reciprocity_O5c`, proved here from Jacobi reciprocity;
* the characters (O.5), `ψ/η = χ_{−1}` (tex 8916–8920, 8982–8985): `extracted_character`;
* the determinant squareclass `m^{-3} ≡ m` (tex 8888–8890, 8974–8975, 9033–9034):
  `extracted_det_squareclass`, `extracted_det`.

All theorems are PROVED. That Serre's formulas are the Hilbert symbols of `ℚ_p` and `ℝ` is GLUE
(J.-P. Serre, *A Course in Arithmetic*, GTM 7, Ch. III §1.1 and §1.2 Theorem 1, with `ε, ω` from
Ch. II §3.3; locators UNVERIFIED); here the formulas are definitions, and only they are used.
-/

namespace ZInQ.Manuscript.RC.Visibility

/-! ### Serre's formulas (tex 8891–8895) -/

/-- The unit part `u` of `a = p^α u`, `α = v_p(a)` (`padicValInt p a`), i.e. `a / p^α` (an exact
division). Kind: definition (tex 8893–8895, Serre's decomposition `a = p^α u`). -/
def unitPart (p : ℕ) (a : ℤ) : ℤ := a / (p : ℤ) ^ padicValInt p a

/-- Serre's `ε(u) = (u − 1)/2 (mod 2)` for an odd integer `u`, as an element of `ℤ/2`.
Kind: definition (tex 8895; Serre, Ch. II §3.3, UNVERIFIED). -/
def epsTwo (u : ℤ) : ZMod 2 := ((u - 1) / 2 : ℤ)

/-- Serre's `ω(u) = (u² − 1)/8 (mod 2)` for an odd integer `u`, as an element of `ℤ/2`. It enters
the formula at two (tex 8891–8895) only through the terms `αω(v) + βω(u)`, which vanish for the odd
entries used there. Kind: definition (Serre, Ch. II §3.3, UNVERIFIED). -/
def omegaTwo (u : ℤ) : ZMod 2 := ((u ^ 2 - 1) / 8 : ℤ)

/-- **Serre's formula at an odd prime** (tex 8891–8894): for nonzero `a = p^α u`, `b = p^β v` with
`p ∤ uv`, `(a, b)_p = (−1)^{αβ(p−1)/2} (u/p)^β (v/p)^α`. The symbol `(u/p)` is written
`jacobiSym u p`, which is the Legendre symbol `legendreSym p u` for a prime `p`
(`hilbertOdd_eq_legendreSym`); this lets the products over prime divisors below be formed without a
primality instance. Kind: definition; GLUE: for an odd prime `p` this is the Hilbert symbol of `ℚ_p`
(Serre, *A Course in Arithmetic*, Ch. III §1.2 Theorem 1, UNVERIFIED). -/
def hilbertOdd (p : ℕ) (a b : ℤ) : ℤ :=
  (-1) ^ (padicValInt p a * padicValInt p b * ((p - 1) / 2)) *
    jacobiSym (unitPart p a) p ^ padicValInt p b * jacobiSym (unitPart p b) p ^ padicValInt p a

/-- **Serre's formula at two** (tex 8891–8895): for nonzero `a = 2^α u`, `b = 2^β v` with `u, v` odd,
`(a, b)_2 = (−1)^{ε(u)ε(v) + αω(v) + βω(u)}`; the exponent is computed in `ℤ/2` and `(−1)^e` is
`(−1)^{e.val}`. Kind: definition; GLUE: this is the Hilbert symbol of `ℚ₂` (Serre, Ch. III §1.2
Theorem 1, UNVERIFIED). -/
def hilbertTwo (a b : ℤ) : ℤ :=
  (-1) ^ (epsTwo (unitPart 2 a) * epsTwo (unitPart 2 b) +
      (padicValInt 2 a : ZMod 2) * omegaTwo (unitPart 2 b) +
      (padicValInt 2 b : ZMod 2) * omegaTwo (unitPart 2 a)).val

/-- **The infinite symbol** (tex 8912): `(a, b)_∞ = −1` if `a < 0` and `b < 0`, and `1` otherwise.
Kind: definition; GLUE: this is the Hilbert symbol of `ℝ` (Serre, Ch. III §1.1, UNVERIFIED). -/
def hilbertInf (a b : ℤ) : ℤ := if a < 0 ∧ b < 0 then -1 else 1

/-- The finite symbol at a prime `p`: `hilbertTwo` at `p = 2` and `hilbertOdd p` otherwise
(tex 8909, 8912–8914). Kind: definition. -/
def hilbertAt (p : ℕ) (a b : ℤ) : ℤ := if p = 2 then hilbertTwo a b else hilbertOdd p a b

/-! ### The symbols at odd primes (tex 8891–8894, 8899, 8912–8914) -/

/-- **PROVED (tex 8893–8894).** The unit part of an integer prime to `p` is the integer itself. -/
theorem unitPart_of_not_dvd {p : ℕ} {a : ℤ} (h : ¬ (p : ℤ) ∣ a) : unitPart p a = a := by
  rw [unitPart, padicValInt.eq_zero_of_not_dvd h, pow_zero, Int.ediv_one]

/-- **PROVED (tex 8891–8894).** `hilbertOdd` is Serre's formula with Legendre symbols:
`(a, b)_p = (−1)^{αβ(p−1)/2} (u/p)^β (v/p)^α` with `u = a/p^α`, `v = b/p^β`. -/
theorem hilbertOdd_eq_legendreSym (p : ℕ) [Fact p.Prime] (a b : ℤ) :
    hilbertOdd p a b =
      (-1) ^ (padicValInt p a * padicValInt p b * ((p - 1) / 2)) *
        legendreSym p (unitPart p a) ^ padicValInt p b *
          legendreSym p (unitPart p b) ^ padicValInt p a := by
  rw [hilbertOdd, jacobiSym.legendreSym.to_jacobiSym, jacobiSym.legendreSym.to_jacobiSym]

/-- **PROVED (tex 8893–8894).** For `p ∤ u`: `(u, m)_p = (u/p)^{v_p(m)}`, with `(u/p)` written as
`jacobiSym u p` (the form used in the products over prime divisors below). -/
theorem hilbertOdd_unit' {p : ℕ} {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) (m : ℤ) :
    hilbertOdd p u m = jacobiSym u p ^ padicValInt p m := by
  rw [hilbertOdd, padicValInt.eq_zero_of_not_dvd hu, unitPart_of_not_dvd hu]
  simp

/-- **PROVED (tex 8893–8894).** At an odd prime `p ∣ m` and a unit `u`: `(u, m)_p = (u/p)^{v_p(m)}`.
The identity holds for every prime `p` and every `m`; the oddness of `p` is what makes `hilbertOdd p`
the Hilbert symbol. -/
theorem hilbertOdd_unit {p : ℕ} [Fact p.Prime] {u : ℤ} (hu : ¬ (p : ℤ) ∣ u) (m : ℤ) :
    hilbertOdd p u m = legendreSym p u ^ padicValInt p m := by
  rw [hilbertOdd_unit' hu, jacobiSym.legendreSym.to_jacobiSym]

/-- **PROVED (tex 8913–8914).** For `q ∤ m`: `(d, m)_q = (m/q)^{v_q(d)}`, with `(m/q)` written as
`jacobiSym m q`. -/
theorem hilbertOdd_at_divisor' {q : ℕ} {m : ℤ} (hm : ¬ (q : ℤ) ∣ m) (d : ℤ) :
    hilbertOdd q d m = jacobiSym m q ^ padicValInt q d := by
  rw [hilbertOdd, padicValInt.eq_zero_of_not_dvd hm, unitPart_of_not_dvd hm]
  simp

/-- **PROVED (tex 8913–8914).** At an odd prime `q ∣ d` with `q ∤ m`: `(d, m)_q = (m/q)^{v_q(d)}`.
The identity holds for every prime `q` and every `d`. -/
theorem hilbertOdd_at_divisor {q : ℕ} [Fact q.Prime] {m : ℤ} (hm : ¬ (q : ℤ) ∣ m) (d : ℤ) :
    hilbertOdd q d m = legendreSym q m ^ padicValInt q d := by
  rw [hilbertOdd_at_divisor' hm, jacobiSym.legendreSym.to_jacobiSym]

/-- **PROVED (tex 8899, 8912–8913, "all other finite symbols are one").** If `p` divides neither
`a` nor `b`, then `(a, b)_p = 1`. The identity holds for every `p`. -/
theorem hilbertOdd_of_not_dvd {p : ℕ} {a b : ℤ} (ha : ¬ (p : ℤ) ∣ a) (hb : ¬ (p : ℤ) ∣ b) :
    hilbertOdd p a b = 1 := by
  rw [hilbertOdd, padicValInt.eq_zero_of_not_dvd ha, padicValInt.eq_zero_of_not_dvd hb]
  simp

/-! ### The symbol at two (tex 8894–8898) -/

/-- **PROVED (tex 8894–8895).** An odd integer is a `2`-adic unit: `2 ∤ u`. -/
theorem two_not_dvd_of_odd {u : ℤ} (hu : Odd u) : ¬ ((2 : ℕ) : ℤ) ∣ u := by
  rintro ⟨k, hk⟩
  obtain ⟨j, hj⟩ := hu
  push_cast at hk
  omega

/-- **PROVED (tex 8897–8898).** `ε(u) = 0` for `u ≡ 1 (mod 4)`. -/
theorem epsTwo_of_one {u : ℤ} (h : u % 4 = 1) : epsTwo u = 0 := by
  rw [epsTwo, ← ZMod.intCast_mod, show (u - 1) / 2 % ((2 : ℕ) : ℤ) = 0 by push_cast; omega]
  rfl

/-- **PROVED (tex 8897–8898).** `ε(u) = 1` for `u ≡ 3 (mod 4)`. -/
theorem epsTwo_of_three {u : ℤ} (h : u % 4 = 3) : epsTwo u = 1 := by
  rw [epsTwo, ← ZMod.intCast_mod, show (u - 1) / 2 % ((2 : ℕ) : ℤ) = 1 by push_cast; omega]
  rfl

/-- **PROVED (tex 8894–8895).** For odd `u, m`: `(u, m)_2 = (−1)^{((u−1)/2)((m−1)/2)}`, which is `−1`
exactly when `u ≡ m ≡ 3 (mod 4)`. -/
theorem hilbertTwo_odd_odd {u m : ℤ} (hu : Odd u) (hm : Odd m) :
    hilbertTwo u m = if u % 4 = 3 ∧ m % 4 = 3 then -1 else 1 := by
  rw [hilbertTwo, padicValInt.eq_zero_of_not_dvd (two_not_dvd_of_odd hu),
    padicValInt.eq_zero_of_not_dvd (two_not_dvd_of_odd hm),
    unitPart_of_not_dvd (two_not_dvd_of_odd hu), unitPart_of_not_dvd (two_not_dvd_of_odd hm)]
  simp only [Nat.cast_zero, zero_mul, add_zero]
  have hu' : u % 2 = 1 := Int.odd_iff.mp hu
  have hm' : m % 2 = 1 := Int.odd_iff.mp hm
  rcases (show u % 4 = 1 ∨ u % 4 = 3 by omega) with h1 | h1 <;>
  rcases (show m % 4 = 1 ∨ m % 4 = 3 by omega) with h2 | h2
  · rw [epsTwo_of_one h1, epsTwo_of_one h2, ite_eq_right (by omega)]; rfl
  · rw [epsTwo_of_one h1, epsTwo_of_three h2, ite_eq_right (by omega)]; rfl
  · rw [epsTwo_of_three h1, epsTwo_of_one h2, ite_eq_right (by omega)]; rfl
  · rw [epsTwo_of_three h1, epsTwo_of_three h2, ite_eq_left ⟨h1, h2⟩]; rfl

/-- **PROVED (tex 8894–8895), the displayed form.** For odd `u, m`:
`(u, m)_2 = (−1)^{((u−1)/2)((m−1)/2)}` (the parity of an integer exponent read through `natAbs`). -/
theorem hilbertTwo_odd_odd' {u m : ℤ} (hu : Odd u) (hm : Odd m) :
    hilbertTwo u m = (-1) ^ ((u - 1) / 2 * ((m - 1) / 2)).natAbs := by
  rw [hilbertTwo_odd_odd hu hm]
  have hu' : u % 2 = 1 := Int.odd_iff.mp hu
  have hm' : m % 2 = 1 := Int.odd_iff.mp hm
  split_ifs with h
  · have hodd : Odd ((u - 1) / 2 * ((m - 1) / 2)) := by
      rw [Int.odd_mul, Int.odd_iff, Int.odd_iff]; omega
    rw [Odd.neg_one_pow (Int.natAbs_odd.mpr hodd)]
  · have hev : Even ((u - 1) / 2 * ((m - 1) / 2)) := by
      rw [Int.even_mul, Int.even_iff, Int.even_iff]; omega
    rw [Even.neg_one_pow (Int.natAbs_even.mpr hev)]

/-- **PROVED (tex 8896–8898).** For `m ≡ 3 (mod 4)` and odd `u`: `(u, m)_2 = 1` if `u ≡ 1 (mod 4)`
and `−1` otherwise. -/
theorem hilbertTwo_of_three_mod_four {u m : ℤ} (hm : m % 4 = 3) (hu : Odd u) :
    hilbertTwo u m = if u % 4 = 1 then 1 else -1 := by
  have hm' : Odd m := Int.odd_iff.mpr (by omega)
  have hu' : u % 2 = 1 := Int.odd_iff.mp hu
  rw [hilbertTwo_odd_odd hu hm']
  by_cases h : u % 4 = 1
  · rw [ite_eq_right (by omega), ite_eq_left h]
  · rw [ite_eq_left ⟨by omega, hm⟩, ite_eq_right h]

/-- **PROVED (tex 8897–8898), the displayed form.** For `m ≡ 3 (mod 4)` and odd `u`, the second
factor is `(−1)^{(u−1)/2}`. -/
theorem hilbertTwo_of_three_mod_four' {u m : ℤ} (hm : m % 4 = 3) (hu : Odd u) :
    hilbertTwo u m = (-1) ^ ((u - 1) / 2).natAbs := by
  have hu' : u % 2 = 1 := Int.odd_iff.mp hu
  rw [hilbertTwo_of_three_mod_four hm hu]
  split_ifs with h
  · have hev : Even ((u - 1) / 2) := by rw [Int.even_iff]; omega
    rw [Even.neg_one_pow (Int.natAbs_even.mpr hev)]
  · have hodd : Odd ((u - 1) / 2) := by rw [Int.odd_iff]; omega
    rw [Odd.neg_one_pow (Int.natAbs_odd.mpr hodd)]

/-- **PROVED (tex 8898).** For `m ≡ 3 (mod 4)` the factor `u ↦ (u, m)_2` is trivial on
`1 + 4ℤ₂`: `u ≡ 1 (mod 4)` gives `(u, m)_2 = 1`. -/
theorem hilbertTwo_of_one_mod_four {u m : ℤ} (hm : m % 4 = 3) (hu : u % 4 = 1) :
    hilbertTwo u m = 1 := by
  rw [hilbertTwo_of_three_mod_four hm (Int.odd_iff.mpr (by omega)), ite_eq_left hu]

/-! ### (O.5c) and Hilbert reciprocity in this case (tex 8903–8915) -/

/-- **PROVED (tex 8910).** The Jacobi symbol as a product over the prime factorization:
`(a/b) = ∏_{q ∣ b} (a/q)^{v_q(b)}` for `b ≠ 0`. -/
theorem jacobiSym_eq_prod_primeFactors (a : ℤ) {b : ℕ} (hb : b ≠ 0) :
    jacobiSym a b = ∏ p ∈ b.primeFactors, jacobiSym a p ^ b.factorization p := by
  rw [Nat.multiplicative_factorization (fun n => jacobiSym a n) ?_ (jacobiSym.one_right a) hb]
  · rw [Finsupp.prod, Nat.support_factorization]
    exact Finset.prod_congr rfl fun p _ => jacobiSym.pow_right a p _
  · intro x y hxy
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · rw [Nat.coprime_zero_left] at hxy
      subst hxy
      simp [jacobiSym.one_right]
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · rw [Nat.coprime_zero_right] at hxy
      subst hxy
      simp [jacobiSym.one_right]
    exact jacobiSym.mul_right' a hx.ne' hy.ne'

/-- **PROVED (tex 8903, 8913).** A prime dividing `m` does not divide `d` when `d, m` are coprime. -/
theorem coprime_prime_not_dvd {p d m : ℕ} (hp : p.Prime) (hpm : p ∣ m) (hdm : Nat.Coprime d m) :
    ¬ (p : ℤ) ∣ (d : ℤ) := by
  rw [Int.natCast_dvd_natCast]
  intro hpd
  have h1 : p ∣ Nat.gcd d m := Nat.dvd_gcd hpd hpm
  rw [hdm.gcd_eq_one, Nat.dvd_one] at h1
  exact hp.one_lt.ne' h1

/-- **PROVED (tex 8909, 8912).** The prime factors of an odd number are different from `2`. -/
theorem ne_two_of_mem_primeFactors_of_odd {p n : ℕ} (hn : Odd n) (hp : p ∈ n.primeFactors) :
    p ≠ 2 := by
  rintro rfl
  exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))

/-- **PROVED ((O.5c), tex 8907–8915).** For odd coprime `d, m > 0`:
`(∏_{p ∣ m} (d, m)_p) · (d, m)_2 = (m/d)`. The odd part is `∏_{p ∣ m} (d/p)^{v_p(m)} = (d/m)`
(`hilbertOdd_unit'`), the dyadic factor is `(−1)^{((d−1)/2)((m−1)/2)}` (`hilbertTwo_odd_odd`), and
Jacobi reciprocity turns their product into `(m/d)`; the dyadic factor is not discarded. -/
theorem O5c {d m : ℕ} (hd : Odd d) (hm : Odd m) (hdm : Nat.Coprime d m) :
    (∏ p ∈ m.primeFactors, hilbertOdd p d m) * hilbertTwo d m = jacobiSym m d := by
  have h1 : ∏ p ∈ m.primeFactors, hilbertOdd p d m = jacobiSym d m := by
    rw [jacobiSym_eq_prod_primeFactors d hm.pos.ne']
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [hilbertOdd_unit' (coprime_prime_not_dvd hpp (Nat.dvd_of_mem_primeFactors hp) hdm),
      padicValInt.of_nat, Nat.factorization_def m hpp]
  have hd' : Odd (d : ℤ) := by exact_mod_cast hd
  have hm' : Odd (m : ℤ) := by exact_mod_cast hm
  rw [h1, hilbertTwo_odd_odd hd' hm']
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hd) with hd4 | hd4 <;>
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm) with hm4 | hm4
  · rw [ite_eq_right (by omega), mul_one, jacobiSym.quadratic_reciprocity_one_mod_four hd4 hm]
  · rw [ite_eq_right (by omega), mul_one, jacobiSym.quadratic_reciprocity_one_mod_four hd4 hm]
  · rw [ite_eq_right (by omega), mul_one, jacobiSym.quadratic_reciprocity_one_mod_four' hd hm4]
  · rw [ite_eq_left (by omega), jacobiSym.quadratic_reciprocity_three_mod_four hd4 hm4]
    ring

/-- **PROVED ((O.5c), tex 8907–8910), with the product over `p ∣ 2m` as displayed.** For odd coprime
`d, m > 0`: `∏_{p ∣ 2m} (d, m)_p = (m/d)`. -/
theorem O5c' {d m : ℕ} (hd : Odd d) (hm : Odd m) (hdm : Nat.Coprime d m) :
    ∏ p ∈ (2 * m).primeFactors, hilbertAt p d m = jacobiSym m d := by
  have hpf : (2 * m).primeFactors = {2} ∪ m.primeFactors := by
    rw [Nat.primeFactors_mul two_ne_zero hm.pos.ne', Nat.prime_two.primeFactors]
  have h2m : Disjoint ({2} : Finset ℕ) m.primeFactors := by
    rw [Finset.disjoint_singleton_left]
    exact fun h => ne_two_of_mem_primeFactors_of_odd hm h rfl
  have hA : ∏ p ∈ m.primeFactors, hilbertAt p d m = ∏ p ∈ m.primeFactors, hilbertOdd p d m :=
    Finset.prod_congr rfl fun p hp => by
      rw [hilbertAt, ite_eq_right (ne_two_of_mem_primeFactors_of_odd hm hp)]
  rw [hpf, Finset.prod_union h2m, Finset.prod_singleton, hA, hilbertAt, ite_eq_left rfl, mul_comm,
    O5c hd hm hdm]

/-- **PROVED ((O.5c), tex 8910, 8913–8914).** For coprime `d, m` with `d` odd:
`∏_{q ∣ d} (d, m)_q = ∏_{q ∣ d} (m/q)^{v_q(d)} = (m/d)`. -/
theorem O5c_divisor_side {d m : ℕ} (hd : Odd d) (hdm : Nat.Coprime d m) :
    ∏ q ∈ d.primeFactors, hilbertOdd q d m = jacobiSym m d := by
  rw [jacobiSym_eq_prod_primeFactors m hd.pos.ne']
  refine Finset.prod_congr rfl fun q hq => ?_
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  rw [hilbertOdd_at_divisor' (coprime_prime_not_dvd hqp (Nat.dvd_of_mem_primeFactors hq) hdm.symm),
    padicValInt.of_nat, Nat.factorization_def d hqp]

/-- **PROVED (tex 8911–8914, Hilbert reciprocity in this case).** For odd coprime `d, m > 0`:
`(∏_{p ∣ 2md} (d, m)_p) · (d, m)_∞ = 1`. The infinite symbol is one (`m, d > 0`), the symbols at
primes outside `2md` are one (`hilbertOdd_of_not_dvd`), the product over `p ∣ 2m` is `(m/d)` (`O5c'`)
and the product over `q ∣ d` is `(m/d)` (`O5c_divisor_side`), and `(m/d)² = 1`. -/
theorem hilbert_reciprocity_O5c {d m : ℕ} (hd : Odd d) (hm : Odd m) (hdm : Nat.Coprime d m) :
    (∏ p ∈ (2 * m * d).primeFactors, hilbertAt p d m) * hilbertInf d m = 1 := by
  have hpf : (2 * m * d).primeFactors = (2 * m).primeFactors ∪ d.primeFactors :=
    Nat.primeFactors_mul (mul_ne_zero two_ne_zero hm.pos.ne') hd.pos.ne'
  have hdisj : Disjoint (2 * m).primeFactors d.primeFactors := by
    rw [Nat.primeFactors_mul two_ne_zero hm.pos.ne', Nat.prime_two.primeFactors,
      Finset.disjoint_union_left, Finset.disjoint_singleton_left]
    exact ⟨fun h => ne_two_of_mem_primeFactors_of_odd hd h rfl, hdm.symm.disjoint_primeFactors⟩
  have hB : ∏ p ∈ d.primeFactors, hilbertAt p d m = ∏ p ∈ d.primeFactors, hilbertOdd p d m :=
    Finset.prod_congr rfl fun p hp => by
      rw [hilbertAt, ite_eq_right (ne_two_of_mem_primeFactors_of_odd hd hp)]
  have hinf : hilbertInf d m = 1 := by
    rw [hilbertInf, ite_eq_right]
    rintro ⟨h, -⟩
    exact absurd h (not_lt.mpr (Int.natCast_nonneg d))
  have hsq : jacobiSym m d ^ 2 = 1 := by
    apply jacobiSym.sq_one
    rw [Int.gcd_natCast_natCast]
    exact hdm.symm
  rw [hpf, Finset.prod_union hdisj, hB, hinf, O5c' hd hm hdm, O5c_divisor_side hd hdm, mul_one,
    ← sq, hsq]

/-! ### The characters (O.5) (tex 8916–8920, 8982–8985) -/

/-- **PROVED ((O.5), tex 8916–8920 and 8982–8985).** Let `d > 0` be odd (in the text `d` is prime to
the complete level, whose prescribed support contains `2`: tex 8498, 8517) and `e = η_B(d)`. Then
`ψ(d) = η(d) χ_{−1}(d)` for `ψ = η_B (m/·)` and `η = η_B χ_{h_*}`, `h_* = −m`:
`e (m/d) = (e (−m/d)) (−1/d)`; moreover `(−1/d) = χ₄(d)`, the character of conductor `4`, i.e.
`χ_{−1}`. Here `χ_{h_*}(d)` is the Kronecker symbol `(h_*/d)`: as `h_* = −m ≡ 1 (mod 4)`, `h_*` is a
discriminant, `χ_{h_*}` is a Dirichlet character modulo `m`, and at an odd `d > 0` the Kronecker
symbol is by definition the Jacobi symbol, so `χ_{h_*}(d) = (−m/d)`. Since `χ_{h_*}(d)² = 1` for `d`
prime to `m`, this is the displayed quotient `η_B(d)(m/d) / (η_B(d)χ_{h_*}(d)) = (−1/d)`. -/
theorem extracted_character {R : Type*} [CommRing R] (e : R) (m : ℕ) {d : ℕ} (hd : Odd d) :
    e * (jacobiSym m d : R) = (e * (jacobiSym (-m) d : R)) * (jacobiSym (-1) d : R) ∧
      (jacobiSym (-1) d : R) = (ZMod.χ₄ d : R) := by
  refine ⟨?_, by rw [jacobiSym.at_neg_one hd]⟩
  have h1 : jacobiSym (-1) d * jacobiSym (-1) d = 1 := by
    rw [← jacobiSym.mul_left]
    norm_num [jacobiSym.one_left]
  have h : jacobiSym (m : ℤ) d = jacobiSym (-(m : ℤ)) d * jacobiSym (-1) d := by
    rw [show (-(m : ℤ)) = (-1) * m by ring, jacobiSym.mul_left, mul_comm (jacobiSym (-1) d),
      mul_assoc, h1, mul_one]
  rw [h]
  push_cast
  ring

/-! ### The determinant squareclass of the extracted form (tex 8888–8890, 8974–8975, 9033–9034) -/

/-- **PROVED (tex 8888–8890, 8974–8975, 9033–9034).** For `m ≠ 0`:
`m^{-3} δ = (m δ) (m^{-2})²`, so the determinant `m^{-3} δ` of `Q_B/m` (where `δ = det Q_B`) has the
squareclass of `m δ`. -/
theorem extracted_det_squareclass {K : Type*} [Field K] {m : K} (hm : m ≠ 0) (δ : K) :
    (m⁻¹) ^ 3 * δ = (m * δ) * ((m⁻¹) ^ 2) ^ 2 := by
  field_simp

/-- **PROVED (tex 8862–8863, 8888–8890, 8974–8975, 9033–9034).** For the ternary form
`Q(x) = xᵀAx` and `m ≠ 0`, the matrix of `Q/m` is `m⁻¹ A` and `det(m⁻¹ A) = m^{-3} det A`, which is
`m det A` times a square; if `det A = s²` (squareclass one, as for `Q_B`) it is `m` times a square. -/
theorem extracted_det {K : Type*} [Field K] {m : K} (hm : m ≠ 0) (A : Matrix (Fin 3) (Fin 3) K) :
    (m⁻¹ • A).det = (m⁻¹) ^ 3 * A.det ∧
      (m⁻¹ • A).det = (m * A.det) * ((m⁻¹) ^ 2) ^ 2 ∧
        ∀ s : K, A.det = s ^ 2 → (m⁻¹ • A).det = m * (s * (m⁻¹) ^ 2) ^ 2 := by
  have h : (m⁻¹ • A).det = (m⁻¹) ^ 3 * A.det := by rw [Matrix.det_smul, Fintype.card_fin]
  refine ⟨h, h.trans (extracted_det_squareclass hm _), fun s hs => ?_⟩
  rw [h.trans (extracted_det_squareclass hm _), hs]
  ring

end ZInQ.Manuscript.RC.Visibility
