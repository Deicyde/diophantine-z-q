import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

/-! Arithmetic of the eighth-root exponents for Weil reciprocity
(tex 9000–9004). The reduction to Jacobi reciprocity is on-the-spot (c). -/

namespace ZInQ.Manuscript.RC.WeilIndex

open scoped BigOperators

/-- Exponent of the sign, in eighth-root notation. -/
def signExponent (s : ℤ) : ZMod 8 := if s = -1 then 4 else 0

/-- The negative-character Gauss sign for an odd modulus. -/
def oddBase (u : ZMod 4) : ZMod 8 := if ZMod.χ₄ u = -1 then 6 else 0

/-- Exponent at two for a unit residue (u) and valuation parity (e).
These are the standard Gauss sum formulas at moduli four and eight. -/
def dyadicExponent (e : Bool) (u : ZMod 8) : ZMod 8 :=
  if e then -u else if ZMod.χ₄ (ZMod.cast u) = -1 then 1 else -1

theorem signExponent_mul {a b : ℤ} (ha : a = 1 ∨ a = -1)
    (hb : b = 1 ∨ b = -1) : signExponent (a * b) = signExponent a + signExponent b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

private theorem jacobi_sign {a : ℤ} {n : ℕ} (h : a.gcd n = 1) :
    jacobiSym a n = 1 ∨ jacobiSym a n = -1 := jacobiSym.eq_one_or_neg_one h

private theorem qrSign_cases {m n : ℕ} (hm : Odd m) (hn : Odd n) :
    qrSign m n = if ZMod.χ₄ (m : ZMod 4) = -1 ∧ ZMod.χ₄ (n : ZMod 4) = -1 then -1 else 1 := by
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm) with hm₁ | hm₃ <;>
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn) with hn₁ | hn₃
  · simp [qrSign, ZMod.χ₄_nat_one_mod_four hm₁]
  · simp [qrSign, ZMod.χ₄_nat_one_mod_four hm₁]
  · simp [qrSign, ZMod.χ₄_nat_three_mod_four hm₃, jacobiSym.at_neg_one hn,
      ZMod.χ₄_nat_one_mod_four hn₁]
  · simp [qrSign, ZMod.χ₄_nat_three_mod_four hm₃, jacobiSym.at_neg_one hn,
      ZMod.χ₄_nat_three_mod_four hn₃]

private theorem oddBase_mul {m n : ℕ} (hm : Odd m) (hn : Odd n) :
    oddBase ((m * n : ℕ) : ZMod 4) =
      oddBase (m : ZMod 4) + oddBase (n : ZMod 4) + signExponent (qrSign m n) := by
  rw [qrSign_cases hm hn, Nat.cast_mul]
  simp only [oddBase, map_mul]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hm) with hm₁ | hm₃ <;>
    rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hn) with hn₁ | hn₃ <;>
    first
    | rw [ZMod.χ₄_nat_one_mod_four hm₁, ZMod.χ₄_nat_one_mod_four hn₁]; decide
    | rw [ZMod.χ₄_nat_one_mod_four hm₁, ZMod.χ₄_nat_three_mod_four hn₃]; decide
    | rw [ZMod.χ₄_nat_three_mod_four hm₃, ZMod.χ₄_nat_one_mod_four hn₁]; decide
    | rw [ZMod.χ₄_nat_three_mod_four hm₃, ZMod.χ₄_nat_three_mod_four hn₃]; decide

theorem odd_prod (s : Finset ℕ) (h : ∀ p ∈ s, Odd p) :
    Odd (∏ p ∈ s, p) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    rw [Finset.prod_insert hp]
    exact (h p (Finset.mem_insert_self _ _)).mul (ih fun q hq => h q (Finset.mem_insert_of_mem hq))

theorem prime_coprime_prod {p : ℕ} (hp : p.Prime) {s : Finset ℕ} (hps : p ∉ s)
    (h : ∀ q ∈ s, q.Prime) : p.Coprime (∏ q ∈ s, q) := by
  rw [hp.coprime_iff_not_dvd, hp.prime.dvd_finsetProd_iff]
  rintro ⟨q, hq, hd⟩
  exact hps ((Nat.prime_dvd_prime_iff_eq hp (h q hq)).mp hd ▸ hq)

private theorem jacobiExponent_prod {d : ℤ} (s : Finset ℕ)
    (hd : ∀ p ∈ s, p ≠ 0 ∧ d.gcd p = 1) :
    signExponent (jacobiSym d (∏ p ∈ s, p)) = ∑ p ∈ s, signExponent (jacobiSym d p) := by
  induction s using Finset.induction_on with
  | empty => simp [signExponent]
  | insert p s hp ih =>
    have hg (q : ℕ) (hq : q ∈ s) := hd q (Finset.mem_insert_of_mem hq)
    let n : ℕ := ∏ q ∈ s, q
    have hdprod : d.gcd (n : ℤ) = 1 := by
      simp only [Int.gcd_eq_natAbs, Int.natAbs_natCast]
      rw [← Nat.coprime_iff_gcd_eq_one, Nat.coprime_prod_right_iff]
      intro q hq
      simpa [Int.gcd_eq_natAbs, Nat.coprime_iff_gcd_eq_one] using (hg q hq).2
    rw [Finset.prod_insert hp, Finset.sum_insert hp]
    have : NeZero p := ⟨(hd p (Finset.mem_insert_self _ _)).1⟩
    have : NeZero (∏ q ∈ s, q) := ⟨Finset.prod_ne_zero_iff.mpr fun q hq => (hg q hq).1⟩
    rw [jacobiSym.mul_right, signExponent_mul (jacobi_sign (hd p (Finset.mem_insert_self _ _)).2)
      (jacobi_sign hdprod), ih hg]


/-- The odd-place exponents for a positive odd squarefree coefficient
combine to the Gauss sign of that coefficient. For a prime (p) in the set,
the numerator of the Legendre symbol is the product of the remaining primes. -/
theorem odd_squarefree_exponents (s : Finset ℕ)
    (h : ∀ p ∈ s, p.Prime ∧ Odd p) :
    (∑ p ∈ s, (oddBase (p : ZMod 4) +
      signExponent (jacobiSym ((∏ q ∈ s.erase p, q : ℕ) : ℤ) p))) =
      oddBase ((∏ p ∈ s, p : ℕ) : ZMod 4) := by
  induction s using Finset.induction_on with
  | empty => simp [oddBase]
  | insert p s hp ih =>
    let n := ∏ q ∈ s, q
    have hP := h p (Finset.mem_insert_self _ _)
    have hs (q : ℕ) (hq : q ∈ s) := h q (Finset.mem_insert_of_mem hq)
    have hno : Odd n := odd_prod s fun q hq => (hs q hq).2
    have hc : p.Coprime n := prime_coprime_prod hP.1 hp fun q hq => (hs q hq).1
    have hpq (q : ℕ) (hq : q ∈ s) : p.gcd q = 1 :=
      (hP.1.coprime_iff_not_dvd.mpr (fun hd =>
        hp ((Nat.prime_dvd_prime_iff_eq hP.1 (hs q hq).1).mp hd ▸ hq))).gcd_eq_one
    have hsplit (q : ℕ) (hq : q ∈ s) :
        signExponent (jacobiSym ((∏ r ∈ (insert p s).erase q, r : ℕ) : ℤ) q) =
          signExponent (jacobiSym (p : ℤ) q) +
          signExponent (jacobiSym ((∏ r ∈ s.erase q, r : ℕ) : ℤ) q) := by
      have hpq' : p ≠ q := fun he => hp (he ▸ hq)
      have hp' : p ∉ s.erase q := fun hmem => hp (Finset.mem_of_mem_erase hmem)
      rw [Finset.erase_insert_of_ne hpq', Finset.prod_insert hp', Nat.cast_mul,
        jacobiSym.mul_left]
      apply signExponent_mul
      · exact jacobi_sign (by simpa [Int.gcd_eq_natAbs] using hpq q hq)
      · have hh := prime_coprime_prod (hs q hq).1 (Finset.notMem_erase q s)
            (fun r hr => (hs r (Finset.mem_of_mem_erase hr)).1)
        simpa [Int.gcd_eq_natAbs] using jacobi_sign (a := ((∏ r ∈ s.erase q, r : ℕ) : ℤ))
          (n := q) (by simpa only [Int.gcd_eq_natAbs, Int.natAbs_natCast, Nat.gcd_comm] using hh.gcd_eq_one)
    have hqp : (n : ℤ).gcd p = 1 := by
      simpa [Int.gcd_eq_natAbs, Nat.gcd_comm] using hc.gcd_eq_one
    have hpn : (p : ℤ).gcd n = 1 := by
      simpa [Int.gcd_eq_natAbs] using hc.gcd_eq_one
    have hqr := jacobiSym.quadratic_reciprocity' hno hP.2
    have hcancel : signExponent (jacobiSym (n : ℤ) p) +
        signExponent (jacobiSym (p : ℤ) n) = signExponent (qrSign p n) := by
      rw [← signExponent_mul (jacobi_sign hqp) (jacobi_sign hpn), hqr,
        mul_assoc, ← pow_two, jacobiSym.sq_one hpn, mul_one]
    rw [Finset.sum_insert hp, Finset.erase_insert hp, Finset.prod_insert hp, oddBase_mul hP.2 hno]
    change oddBase (p : ZMod 4) + signExponent (jacobiSym (n : ℤ) p) + _ = _
    calc
      _ = oddBase (p : ZMod 4) + signExponent (jacobiSym (n : ℤ) p) +
          ((∑ q ∈ s, signExponent (jacobiSym (p : ℤ) q)) +
            ∑ q ∈ s, (oddBase (q : ZMod 4) +
              signExponent (jacobiSym ((∏ r ∈ s.erase q, r : ℕ) : ℤ) q))) := by
            congr 1
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro q hq
            rw [hsplit q hq]
            ac_rfl
      _ = _ := by
        rw [ih hs, ← jacobiExponent_prod s (fun q hq => by
          exact ⟨(hs q hq).1.ne_zero, by simpa [Int.gcd_eq_natAbs] using hpq q hq⟩)]
        change _ + signExponent (jacobiSym (n : ℤ) p) +
          (signExponent (jacobiSym (p : ℤ) n) + oddBase (n : ZMod 4)) = _
        rw [show ∀ a b c d : ZMod 8, a + b + (c + d) = a + d + (b + c) by
          intros; ac_rfl, hcancel]

/-- The dyadic and real places cancel the combined odd exponent.
The two optional signs are precisely the supplements for (-1) and (2). -/
theorem total_exponent (u : ZMod 8) (hu : IsUnit u) (negative oddValuation : Bool) :
    (if negative then -1 else (1 : ZMod 8)) +
      dyadicExponent oddValuation (if negative then -u else u) +
      (oddBase (ZMod.cast u) +
        (if negative then signExponent (ZMod.χ₄ (ZMod.cast u)) else 0) +
        (if oddValuation then signExponent (ZMod.χ₈ u) else 0)) = 0 := by
  have hu' : (ZMod.cast u : ZMod 2) ≠ 0 :=
    (hu.map (ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2))).ne_zero
  clear hu
  fin_cases u <;> cases negative <;> cases oddValuation <;>
    first | decide | exact False.elim (hu' (by decide))

/-- Sign of a rational coefficient, encoded by its negativity bit. -/
def coefficientSign (negative : Bool) : ℤ := if negative then -1 else 1

/-- The optional contribution of the prime two to the squarefree part. -/
def twoPart (oddValuation : Bool) : ℕ := if oddValuation then 2 else 1

theorem odd_coprime_two {p : ℕ} (hp : Odd p) : p.Coprime 2 := by
  rw [Nat.coprime_comm, Nat.prime_two.coprime_iff_not_dvd]
  intro hd
  have := Nat.mod_eq_zero_of_dvd hd
  have := Nat.odd_iff.mp hp
  omega


/-- Incorporate the two supplementary laws in the sum of odd-place phases. -/
theorem signed_odd_squarefree_exponents (s : Finset ℕ)
    (h : ∀ p ∈ s, p.Prime ∧ Odd p) (negative oddValuation : Bool) :
    let n := ∏ p ∈ s, p
    (∑ p ∈ s, (oddBase (p : ZMod 4) +
      signExponent (jacobiSym (coefficientSign negative * (twoPart oddValuation : ℤ) *
        ((∏ q ∈ s.erase p, q : ℕ) : ℤ)) p))) =
      oddBase (n : ZMod 4) +
        (if negative then signExponent (ZMod.χ₄ (n : ZMod 4)) else 0) +
        (if oddValuation then signExponent (ZMod.χ₈ (n : ZMod 8)) else 0) := by
  classical
  dsimp only
  have hs1 (p : ℕ) (hp : p ∈ s) : (coefficientSign negative).gcd p = 1 := by
    cases negative <;> simp [coefficientSign]
  have hs2 (p : ℕ) (hp : p ∈ s) : ((twoPart oddValuation : ℕ) : ℤ).gcd p = 1 := by
    cases oddValuation
    · simp [twoPart]
    · simpa [twoPart, Int.gcd_eq_natAbs, Nat.gcd_comm] using (odd_coprime_two (h p hp).2).gcd_eq_one
  have ho := odd_prod s fun p hp => (h p hp).2
  calc
    _ = (∑ p ∈ s, (oddBase (p : ZMod 4) +
        signExponent (jacobiSym ((∏ q ∈ s.erase p, q : ℕ) : ℤ) p))) +
        (∑ p ∈ s, signExponent (jacobiSym (coefficientSign negative) p)) +
        (∑ p ∈ s, signExponent (jacobiSym (twoPart oddValuation : ℤ) p)) := by
          simp only [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p hp
          have hh := (prime_coprime_prod (h p hp).1 (Finset.notMem_erase p s)
            (fun q hq => (h q (Finset.mem_of_mem_erase hq)).1)).symm
          have hunit := jacobi_sign (a := ((∏ q ∈ s.erase p, q : ℕ) : ℤ)) (n := p)
            (by simpa only [Int.gcd_eq_natAbs, Int.natAbs_natCast] using hh.gcd_eq_one)
          rw [jacobiSym.mul_left, jacobiSym.mul_left, signExponent_mul _ hunit,
            signExponent_mul (jacobi_sign (hs1 p hp)) (jacobi_sign (hs2 p hp))]
          · ac_rfl
          · rcases jacobi_sign (hs1 p hp) with h₁ | h₁ <;>
              rcases jacobi_sign (hs2 p hp) with h₂ | h₂ <;> simp [h₁, h₂]
    _ = _ := by
      rw [odd_squarefree_exponents s h, ← jacobiExponent_prod s
        (fun p hp => ⟨(h p hp).1.ne_zero, hs1 p hp⟩), ← jacobiExponent_prod s
        (fun p hp => ⟨(h p hp).1.ne_zero, hs2 p hp⟩)]
      cases negative <;> cases oddValuation <;>
        simp [coefficientSign, twoPart, jacobiSym.at_neg_one ho, jacobiSym.at_two ho, signExponent]

#print axioms odd_coprime_two
#print axioms signed_odd_squarefree_exponents
#print axioms signExponent_mul
#print axioms jacobi_sign
#print axioms qrSign_cases
#print axioms oddBase_mul
#print axioms odd_prod
#print axioms prime_coprime_prod
#print axioms jacobiExponent_prod
#print axioms odd_squarefree_exponents
#print axioms total_exponent

end ZInQ.Manuscript.RC.WeilIndex
