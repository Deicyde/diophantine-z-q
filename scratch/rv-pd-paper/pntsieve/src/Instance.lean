import PrimeNumberTheoremAnd.Mathlib.NumberTheory.Sieve.Selberg
/-! The sieve data of pd-paper §4.3 form a `SelbergSieve` (referee check). -/
open ArithmeticFunction Finset

noncomputable section
namespace RvPd

/-- the coset map `F(U,V) = (ℓU)² + (b + ℓV)²` -/
def F (ℓ b : ℕ) (x : ℤ × ℤ) : ℕ := ((ℓ * x.1) ^ 2 + (b + ℓ * x.2) ^ 2).toNat

/-- the box `I₁ × I₂` with `T = ⌊√N⌋` -/
def box (ℓ b N : ℕ) : Finset (ℤ × ℤ) :=
  (Icc (-((Nat.sqrt N / ℓ : ℕ) : ℤ)) ((Nat.sqrt N / ℓ : ℕ) : ℤ)) ×ˢ
    ((Icc (-(Nat.sqrt N : ℤ)) (Nat.sqrt N)).filter fun V => |(b : ℤ) + ℓ * V| ≤ Nat.sqrt N)

def sievePrimes (ℓ w : ℕ) : Finset ℕ :=
  (range (w + 1)).filter fun q => q.Prime ∧ q % 4 = 1 ∧ q ≠ ℓ

def nuF : ArithmeticFunction ℝ := prodPrimeFactors fun q => (2 * (q : ℝ) - 1) / (q : ℝ) ^ 2

lemma mem_of_prime_dvd {ℓ w p : ℕ} (hp : p.Prime) (h : p ∣ ∏ q ∈ sievePrimes ℓ w, q) :
    p ∈ sievePrimes ℓ w := by
  obtain ⟨q, hq, hpq⟩ := (Prime.dvd_finsetProd_iff hp.prime _).1 h
  have hqp : q.Prime := (mem_filter.1 hq).2.1
  rwa [(Nat.prime_dvd_prime_iff_eq hp hqp).1 hpq]

lemma nuF_prime {p : ℕ} (hp : p.Prime) : nuF p = (2 * (p : ℝ) - 1) / (p : ℝ) ^ 2 := by
  simp [nuF, hp.ne_zero, hp.primeFactors]

def sieve (ℓ b N w : ℕ) (hw : 1 ≤ w) : SelbergSieve where
  support := (box ℓ b N).image (F ℓ b)
  prodPrimes := ∏ q ∈ sievePrimes ℓ w, q
  prodPrimes_squarefree := by
    refine Finset.squarefree_prod_of_pairwise_isCoprime (fun q hq r hr hqr => ?_) fun q hq => ?_
    · simp only [Function.onFun, ← Nat.coprime_iff_isRelPrime]
      exact (Nat.coprime_primes (mem_filter.1 hq).2.1 (mem_filter.1 hr).2.1).2 hqr
    · exact (mem_filter.1 hq).2.1.squarefree
  weights n := (((box ℓ b N).filter fun x => F ℓ b x = n).card : ℝ)
  weights_nonneg n := by positivity
  totalMass := ((Nat.sqrt N / ℓ : ℕ) * 2 + 1 : ℝ) *
    (((Icc (-(Nat.sqrt N : ℤ)) (Nat.sqrt N)).filter fun V => |(b : ℤ) + ℓ * V| ≤ Nat.sqrt N).card)
  nu := nuF
  nu_mult := IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime p hp _ := by
    rw [nuF_prime hp]
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    exact div_pos (by linarith) (by positivity)
  nu_lt_one_of_prime p hp _ := by
    rw [nuF_prime hp]
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    rw [div_lt_one (by positivity)]
    nlinarith
  level := (w : ℝ) ^ 2
  one_le_level := by
    have : (1 : ℝ) ≤ w := by exact_mod_cast hw
    nlinarith

/-- `selberg_bound_simple` applies verbatim to these data. -/
example (ℓ b N w : ℕ) (hw : 1 ≤ w) := SelbergSieve.selberg_bound_simple (sieve ℓ b N w hw)

end RvPd
end
#print axioms RvPd.sieve
