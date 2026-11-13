import ZInQKernel.RouteK.Redei.Genus
import ZInQKernel.RouteK.Slots.Dirichlet

/-!
# Rédei's formula, step 5: split primes and Dirichlet's theorem (`docs/research/redei-plan.md` §3.2)

`K = QNeg n`, `O = 𝓞 K`, `n` odd squarefree.

* `exists_absNorm_eq_of_isSquare`: a prime `p ∤ 2n` with `−n` a square mod `p` has a prime of norm
  `p` above it. It is not ramified (`dvd_of_ramified`), and not inert: if `pO` is prime and
  `m² ≡ −n (mod p)`, then `(m + ω)(m − ω) ∈ pO`, so both factors lie in `pO` (it is σ-stable), so
  `p ∣ 2m`, hence `p ∣ m` and `p ∣ n`;
* `exists_chi_eq`: **surjectivity of the genus characters**. Every `ε : primes of n → 𝔽₂` (with
  `Σ ε = 0` when `n ≡ 3 (mod 4)`) is `(χ_q(c))_q` for some class `c`. Take a prime `ℓ` with
  `[ℓ/q] = ε_q` for every `q ∣ n` and `ℓ ≡ 1` or `3 (mod 8)` according to `Σ ε` (the slot lemma
  `exists_prime_slot_bits`: residues, CRT, Dirichlet); Jacobi reciprocity gives
  `(−n/ℓ) = χ₄(ℓ) (ℓ/n) = 1`, so `ℓ` splits, and a prime of norm `ℓ` has the prescribed characters.
-/

noncomputable section

open NumberField Pointwise
open scoped nonZeroDivisors

namespace ZInQ.RouteK.Redei

open ZInQ.RouteK.Rank5b

/-! ### Signs and the Jacobi symbol -/

/-- `∏ (−1)^{f i} = (−1)^{Σ f i}` for bits `f i ∈ 𝔽₂`. -/
theorem prod_ite_bit_eq {ι : Type*} (s : Finset ι) (f : ι → ZMod 2) :
    ∏ i ∈ s, (if f i = 0 then (1 : ℤ) else -1) = if ∑ i ∈ s, f i = 0 then 1 else -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, ih]
    have key : ∀ a b : ZMod 2, ((if a = 0 then (1 : ℤ) else -1) * if b = 0 then 1 else -1) =
        if a + b = 0 then 1 else -1 := by decide
    exact key _ _

/-- The Jacobi symbol is multiplicative over a finite product in its second argument. -/
theorem jacobiSym_finsetProd_right {ι : Type*} (a : ℤ) (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) : jacobiSym a (∏ i ∈ s, f i) = ∏ i ∈ s, jacobiSym a (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [jacobiSym.one_right]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      jacobiSym.mul_right' a (hf i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.2 fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

section Dirichlet

variable (n : ℕ) [NeZero n]

local notation "K" => QNeg n
local notation "O" => 𝓞 (QNeg n)

variable {n}

/-! ### Split primes -/

variable (n) in
/-- A prime `p ∤ 2n` with `−n` a square mod `p` has a prime of norm `p` above it. -/
theorem exists_absNorm_eq_of_isSquare {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n)
    (hsq : IsSquare (-(n : ZMod p))) :
    ∃ P : (Ideal O)⁰, Ideal.absNorm (P : Ideal O) = p := by
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := n)
  obtain ⟨P, hPm, hPl⟩ := exists_maximal_liesOver (n := n) hp
  refine ⟨⟨P, mem_nonZeroDivisors_of_ne_zero (ne_bot_of_liesOver hp P)⟩, ?_⟩
  rcases prime_trichotomy n σ hσ hp P with ⟨-, -, hN⟩ | ⟨hs, hP, -⟩ | ⟨-, h2, -⟩
  · exact hN
  · exfalso
    obtain ⟨r, hr⟩ := hsq
    set m : ℤ := (r.val : ℤ)
    have hm : (p : ℤ) ∣ m ^ 2 + n := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      have : NeZero p := ⟨hp.ne_zero⟩
      have : ((m : ℤ) : ZMod p) = r := by simp only [m, Int.cast_natCast, ZMod.natCast_zmod_val]
      push_cast
      rw [this, pow_two, ← hr]; ring
    obtain ⟨k, hk⟩ := hm
    have hmem : ((m : O) + omegaO n) * ((m : O) - omegaO n) ∈ P := by
      rw [hP, Ideal.mem_span_singleton]
      refine ⟨(k : O), ?_⟩
      have e : ((m : O) + omegaO n) * ((m : O) - omegaO n) = (((m ^ 2 + n : ℤ)) : O) := by
        rw [show ((m : O) + omegaO n) * ((m : O) - omegaO n) = m * m - omegaO n * omegaO n by ring,
          omegaO_sq]
        push_cast; ring
      rw [e, hk]; push_cast; ring
    have hsmul : ∀ x ∈ P, σ • x ∈ P := fun x hx => by
      rw [← hs]; exact Ideal.smul_mem_pointwise_smul σ x P hx
    have e1 : σ • ((m : O) + omegaO n) = (m : O) - omegaO n := by
      rw [smul_add, smul_intCast_O, conj_omegaO σ hσ]; ring
    have e2 : σ • ((m : O) - omegaO n) = (m : O) + omegaO n := by
      rw [smul_sub, smul_intCast_O, conj_omegaO σ hσ]; ring
    have hboth : (m : O) + omegaO n ∈ P ∧ (m : O) - omegaO n ∈ P := by
      rcases Ideal.IsPrime.mem_or_mem inferInstance hmem with h | h
      · exact ⟨h, e1 ▸ hsmul _ h⟩
      · exact ⟨e2 ▸ hsmul _ h, h⟩
    have h2m : (((2 * m : ℤ)) : O) ∈ P := by
      have := Ideal.add_mem P hboth.1 hboth.2
      convert this using 1; push_cast; ring
    rw [intCast_mem_iff_of_liesOver (p := p) P] at h2m
    have hpz := Nat.prime_iff_prime_int.mp hp
    rcases hpz.dvd_mul.1 h2m with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (by exact_mod_cast h))
    · have hn : (p : ℤ) ∣ (n : ℤ) := by
        have h1 : (p : ℤ) ∣ m ^ 2 := dvd_pow h two_ne_zero
        exact (Int.dvd_add_right h1).1 ⟨k, hk⟩
      exact hpn (by exact_mod_cast hn)
  · rcases dvd_of_ramified n hp P h2 with h | ⟨h, -⟩
    · exact absurd h hpn
    · exact absurd h hp2

/-! ### Surjectivity of the genus characters -/

omit [NeZero n] in
theorem ne_two_of_mem_primeFactors (hn : Odd n) {q : ℕ} (hq : q ∈ n.primeFactors) : q ≠ 2 := by
  rintro rfl
  exact (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hq))

variable (n) in
/-- **Surjectivity of the genus characters** (Dirichlet's theorem, CRT, Jacobi reciprocity). The
image of `χ` is all of `𝔽₂^{primes of n}` if `n ≡ 1 (mod 4)` and the sum-zero hyperplane if
`n ≡ 3 (mod 4)`. -/
theorem exists_chi_eq (hn : Odd n) (hsq : Squarefree n) (ε : n.primeFactors → ZMod 2)
    (hε : n % 4 = 3 → ∑ q, ε q = 0) :
    ∃ c : ClassGroup O, ∀ q, chi n q c = Multiplicative.ofAdd (ε q) := by
  classical
  have hodd : ∀ p ∈ n.primeFactors, p.Prime ∧ p ≠ 2 := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp, ne_two_of_mem_primeFactors hn hp⟩
  let b : ℕ → ZMod 2 := fun p => if h : p ∈ n.primeFactors then ε ⟨p, h⟩ else 0
  have ha : Odd (if ∑ q, ε q = 0 then (1 : ℤ) else 3) := by split_ifs <;> decide
  obtain ⟨ℓ, hℓ, -, hℓS, hℓ8, hℓb⟩ := exists_prime_slot_bits n.primeFactors hodd b ha ∅
  have hℓn : ¬ ℓ ∣ n := fun h => hℓS (Nat.mem_primeFactors.2 ⟨hℓ, h, NeZero.ne n⟩)
  have hn4 : n % 4 = 1 ∨ n % 4 = 3 := by have := Nat.odd_iff.1 hn; omega
  have hℓ4 : (∑ q, ε q = 0 → ℓ % 4 = 1) ∧ (∑ q, ε q ≠ 0 → ℓ % 4 = 3) := by
    unfold Int.ModEq at hℓ8
    constructor
    · intro h; rw [ite_eq_left h] at hℓ8; omega
    · intro h; rw [ite_eq_right h] at hℓ8; omega
  have hℓ2 : ℓ ≠ 2 := by
    rintro rfl
    by_cases h : ∑ q, ε q = 0
    · exact absurd (hℓ4.1 h) (by norm_num)
    · exact absurd (hℓ4.2 h) (by norm_num)
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hℓq : ∀ q : n.primeFactors, (q : ℕ) ≠ ℓ := fun q h => hℓS (h ▸ q.2)
  -- the bits `[ℓ/q] = ε q`
  have hbit : ∀ q : n.primeFactors, legBit q ℓ = ε q := fun q => by
    rw [hℓb q q.2]; simp only [b, dite_eq_left q.2]
  -- `(ℓ/n) = (−1)^{Σ ε}`
  have hJn : jacobiSym ℓ n = if ∑ q, ε q = 0 then 1 else -1 := by
    have hprod : n = ∏ q : n.primeFactors, (q : ℕ) := by
      rw [Finset.prod_coe_sort n.primeFactors (fun p => p), Nat.prod_primeFactors_of_squarefree hsq]
    rw [show jacobiSym ℓ n = jacobiSym ℓ (∏ q : n.primeFactors, (q : ℕ)) from congrArg _ hprod,
      jacobiSym_finsetProd_right (ι := n.primeFactors) _ _ (fun q => (q : ℕ))
        fun q _ => (hodd q q.2).1.ne_zero, ← prod_ite_bit_eq]
    refine Finset.prod_congr rfl fun q _ => ?_
    have := Fact.mk (hodd q q.2).1
    rw [← jacobiSym.legendreSym.to_jacobiSym, ← legBit_eq_iff_legendreSym
      (natCast_zmod_ne_zero_of_prime_ne (hodd q q.2).1 hℓ (hℓq q)), hbit q]
  -- `(−n/ℓ) = 1`
  have hJ : jacobiSym (-(n : ℤ)) ℓ = 1 := by
    rw [jacobiSym.neg _ hℓodd]
    by_cases h : ∑ q, ε q = 0
    · rw [ZMod.χ₄_nat_one_mod_four (hℓ4.1 h),
        jacobiSym.quadratic_reciprocity_one_mod_four' hn (hℓ4.1 h), hJn, ite_eq_left h, one_mul]
    · have hn1 : n % 4 = 1 := hn4.resolve_right fun h3 => h (hε h3)
      rw [ZMod.χ₄_nat_three_mod_four (hℓ4.2 h),
        jacobiSym.quadratic_reciprocity_one_mod_four hn1 hℓodd, hJn, ite_eq_right h]
      norm_num
  have := Fact.mk hℓ
  have hsqℓ : IsSquare (-(n : ZMod ℓ)) := by
    have := ZMod.isSquare_of_jacobiSym_eq_one hJ
    push_cast at this
    exact this
  obtain ⟨P, hP⟩ := exists_absNorm_eq_of_isSquare n hℓ hℓ2 hℓn hsqℓ
  refine ⟨ClassGroup.mk0 P, fun q => ?_⟩
  have hqP : ¬ (q : ℕ) ∣ Ideal.absNorm (P : Ideal O) := by
    rw [hP]
    exact fun h => hℓq q ((Nat.prime_dvd_prime_iff_eq (hodd q q.2).1 hℓ).1 h)
  rw [chi_mk0 n hn hsq q P hqP, hP, hbit q]

end Dirichlet

end ZInQ.RouteK.Redei
