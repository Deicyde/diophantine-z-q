import ZInQKernel.Contrib.OneProof.TYZLemma29Genus

/-!
# tyz-genus: the genus character `χ_U = Π_{q ∣ n} χ_q` on ideals prime to `2n`, `n ≡ 1 (mod 4)`

For an integral ideal `I` of `𝓞_{ℚ(√−n)}` with `N I` prime to `2n`:
* `jacobiSym_neg_absNorm`: `(−n / N I) = 1` (split primes have norm `p` and `−n ≡ m² (mod p)`; inert primes
  have norm `p²`);
* `prod_sgn_chi_mk0`: `Π_{q ∣ n} χ_q([I]) = (N I / n) = (n / N I) = χ₄(N I)` (Jacobi reciprocity,
  `n ≡ 1 (mod 4)`).
-/

noncomputable section

open NumberField
open scoped nonZeroDivisors

namespace ZInQ.Contrib.TYZGenusFold

open ZInQ.RouteK.Redei ZInQ.RouteK.Rank5b
open ZInQ.Contrib.TYZGenus.TYZ35 (sgn2 sgnHom)

variable {n : ℕ} [NeZero n]

/-- A nonzero prime ideal of `𝓞_K` lies over a rational prime dividing its norm. -/
theorem exists_prime_liesOver_of_prime {P : Ideal (𝓞 (QNeg n))} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) ∧ p ∣ Ideal.absNorm P := by
  have hmax : P.IsMaximal := hP.isMaximal hP0
  have hN1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hmax.ne_top
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hN1
  obtain ⟨Q, hQm, hQu, hQP⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm' hp P hpd
  have hQ : Q = P := by
    have hle : P ≤ Q := Ideal.le_of_dvd hQP
    exact (hmax.eq_of_le hQm.ne_top hle).symm
  subst hQ
  refine ⟨p, hp, hmax, ⟨?_⟩, hpd⟩
  rw [hQu]

/-- `(−n / N 𝔭) = 1` for a nonzero prime `𝔭` with `N 𝔭` prime to `2n`. -/
theorem jacobiSym_neg_absNorm_prime {P : Ideal (𝓞 (QNeg n))} (hP : P.IsPrime)
    (hP0 : P ≠ ⊥) (hcop : Nat.Coprime (Ideal.absNorm P) (2 * n)) :
    jacobiSym (-(n : ℤ)) (Ideal.absNorm P) = 1 := by
  obtain ⟨p, hp, hmax, hlies, hpd⟩ := exists_prime_liesOver_of_prime hP hP0
  have : Fact p.Prime := ⟨hp⟩
  have hp2n : ¬ p ∣ 2 * n := fun h =>
    hp.one_lt.ne' ((Nat.Coprime.coprime_dvd_left hpd hcop).eq_one_of_dvd h)
  have hpn : ¬ (p : ℤ) ∣ (n : ℤ) := fun h =>
    hp2n (dvd_mul_of_dvd_right (by exact_mod_cast h) 2)
  have hne : ((-(n : ℤ) : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, dvd_neg]; exact hpn
  have hgcd : (-(n : ℤ)).gcd (p : ℤ) = 1 := by
    rw [Int.neg_gcd, Int.gcd_natCast_natCast]
    exact ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpn (by exact_mod_cast h)).symm
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := n)
  have hNP : Ideal.absNorm P = p ∨ Ideal.absNorm P = p ^ 2 := by
    rcases prime_trichotomy n σ hσ hp P with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inl h
  rcases hNP with h | h
  · rw [h]
    obtain ⟨m, hm⟩ := exists_int_sub_mem_of_absNorm P hp h (omegaO n)
    have hmem : (((m ^ 2 + n : ℤ)) : 𝓞 (QNeg n)) ∈ P := by
      have e : (((m ^ 2 + n : ℤ)) : 𝓞 (QNeg n)) = -((omegaO n - m) * (omegaO n + m)) := by
        have := omegaO_sq (n := n)
        push_cast
        linear_combination this
      rw [e]
      exact P.neg_mem_iff.mpr (P.mul_mem_right _ hm)
    rw [intCast_mem_iff_of_liesOver (p := p) P] at hmem
    have hsq : IsSquare (((-(n : ℤ) : ℤ) : ZMod p)) := by
      refine ⟨(m : ZMod p), ?_⟩
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hmem
      push_cast at this ⊢
      linear_combination -this
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    exact (legendreSym.eq_one_iff p hne).mpr hsq
  · rw [h, pow_two, jacobiSym.mul_right' _ hp.ne_zero hp.ne_zero, ← pow_two]
    exact jacobiSym.sq_one hgcd

/-- **`(−n / N I) = 1`** for a nonzero integral ideal `I` with `N I` prime to `2n`. -/
theorem jacobiSym_neg_absNorm (I : Ideal (𝓞 (QNeg n))) (hI : I ≠ ⊥)
    (hcop : Nat.Coprime (Ideal.absNorm I) (2 * n)) :
    jacobiSym (-(n : ℤ)) (Ideal.absNorm I) = 1 := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx =>
    rw [Ideal.isUnit_iff] at hx
    rw [hx, Ideal.absNorm_top]
    exact jacobiSym.one_right _
  | h₃ a p ha hp ih =>
    have hp0 : p ≠ ⊥ := hp.ne_zero
    have hmul : Ideal.absNorm (p * a) = Ideal.absNorm p * Ideal.absNorm a := map_mul _ _ _
    rw [hmul] at hcop ⊢
    have hpa : Ideal.absNorm p ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hp0
    have haa : Ideal.absNorm a ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]; exact ha
    rw [jacobiSym.mul_right' _ hpa haa,
      jacobiSym_neg_absNorm_prime ((Ideal.prime_iff_isPrime hp0).mp hp) hp0
        (Nat.Coprime.coprime_mul_right hcop),
      ih ha (Nat.Coprime.coprime_mul_left hcop), one_mul]

theorem sgn2_ofAdd (b : ZMod 2) : sgn2 (Multiplicative.ofAdd b) = if b = 0 then 1 else -1 := by
  unfold sgn2
  rcases (by decide : ∀ b : ZMod 2, b = 0 ∨ b = 1) b with rfl | rfl <;> decide

/-- **`χ_U([I]) = χ₄(N I)`** for `n ≡ 1 (mod 4)` squarefree and an integral ideal `I` with `N I` prime to `2n`:
`Π_{q ∣ n} χ_q([I]) = (N I / n) = (n / N I) = χ₄(N I) (−n / N I) = χ₄(N I)`. -/
theorem gchar_univ_mk0 (hn4 : n % 4 = 1) (hsq : Squarefree n) (I : (Ideal (𝓞 (QNeg n)))⁰)
    (hcop : Nat.Coprime (Ideal.absNorm (I : Ideal (𝓞 (QNeg n)))) (2 * n))
    (c : ClassGroup (𝓞 (QNeg n))) (hc : ClassGroup.mk0 I = c) :
    ZInQ.Contrib.TYZGenus.TYZ35.gchar n Finset.univ c =
      if Ideal.absNorm (I : Ideal (𝓞 (QNeg n))) % 4 = 1 then 1 else -1 := by
  classical
  set m := Ideal.absNorm (I : Ideal (𝓞 (QNeg n))) with hmdef
  have hn : Odd n := Nat.odd_iff.mpr (by omega)
  have hm : Odd m := by
    rw [Nat.odd_iff]
    have h2 : Nat.Coprime m 2 := Nat.Coprime.coprime_dvd_right (dvd_mul_right 2 n) hcop
    rcases Nat.mod_two_eq_zero_or_one m with h | h
    · exfalso
      have : 2 ∣ m := Nat.dvd_of_mod_eq_zero h
      exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.symm h2) this) (by norm_num)
    · exact h
  have hI0 : (I : Ideal (𝓞 (QNeg n))) ≠ ⊥ := nonZeroDivisors.coe_ne_zero I
  have hJ := jacobiSym_neg_absNorm (I : Ideal (𝓞 (QNeg n))) hI0 hcop
  have hqm : ∀ q : n.primeFactors, ¬ (q : ℕ) ∣ m := fun q h =>
    (Nat.prime_of_mem_primeFactors q.2).one_lt.ne'
      ((Nat.Coprime.coprime_dvd_right (dvd_mul_of_dvd_right (Nat.dvd_of_mem_primeFactors q.2) 2)
        hcop).symm.eq_one_of_dvd h)
  have hterm : ∀ q : n.primeFactors, sgn2 (chi n q c) = jacobiSym m q := by
    intro q
    rw [← hc]
    have hqp := Nat.prime_of_mem_primeFactors q.2
    have := Fact.mk hqp
    rw [chi_mk0 n hn hsq q I (hqm q), sgn2_ofAdd, ← jacobiSym.legendreSym.to_jacobiSym]
    exact ((ZInQ.RouteK.legBit_eq_iff_legendreSym (intCast_natCast_zmod_ne_zero (hqm q)) _).mp rfl).symm
  have hprod : n = ∏ q : n.primeFactors, (q : ℕ) := by
    rw [Finset.prod_coe_sort n.primeFactors (fun p => p), Nat.prod_primeFactors_of_squarefree hsq]
  have hJm : ZInQ.Contrib.TYZGenus.TYZ35.gchar n Finset.univ c = jacobiSym m n := by
    unfold ZInQ.Contrib.TYZGenus.TYZ35.gchar
    rw [Finset.prod_congr rfl fun q _ => hterm q,
      show jacobiSym m n = jacobiSym m (∏ q : n.primeFactors, (q : ℕ)) from congrArg _ hprod,
      jacobiSym_finsetProd_right (ι := n.primeFactors) _ _ (fun q => (q : ℕ))
        fun q _ => (Nat.prime_of_mem_primeFactors q.2).ne_zero]
  rw [hJm, ← jacobiSym.quadratic_reciprocity_one_mod_four hn4 hm]
  rw [jacobiSym.neg _ hm] at hJ
  have hm4 : m % 4 = 1 ∨ m % 4 = 3 := by have := Nat.odd_iff.mp hm; omega
  rcases hm4 with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul] at hJ
    rw [if_pos h]; exact_mod_cast hJ
  · rw [ZMod.χ₄_nat_three_mod_four h] at hJ
    rw [if_neg (by omega)]
    have : jacobiSym (n : ℤ) m = -1 := by linarith
    exact_mod_cast this

end ZInQ.Contrib.TYZGenusFold
