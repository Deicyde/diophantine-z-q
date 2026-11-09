import Mathlib

/-!
# Hypothesis H: the six-contact height estimate

Theorem 4.1 (`thm:height`) of the 11/5 manuscript. Its proof uses Shimura curves,
Buzzard's integral models, modularity at the coefficient prime five and an effective
CM argument, none of which is available in Mathlib. The statement itself concerns
only rational numbers, so it enters the main theorem as an explicit hypothesis.
-/

namespace ZInQ

open scoped BigOperators

/-- The logarithmic height `h(a/b) = log max(|a|, b)` of a rational number in lowest terms. -/
noncomputable def ratHeight (u : ℚ) : ℝ :=
  Real.log (max |(u.num : ℝ)| (u.den : ℝ))

/-- The six contact values `𝒞 = {0, -15, -20, -24, -30, -60}`. -/
def contactSet : Finset ℚ := {0, -15, -20, -24, -30, -60}

open Classical in
/-- `M_S(u)`: the product of the primes `p ∉ S` at which `v_p(u - c)` is positive and odd for
some contact value `c`. Negative valuations of `u` do not contribute. -/
noncomputable def contactSupport (S : Finset ℕ) (u : ℚ) : ℕ :=
  ∏ p ∈ (∏ c ∈ contactSet, (u - c).num.natAbs).primeFactors with
      p ∉ S ∧ ∃ c ∈ contactSet, 0 < padicValRat p (u - c) ∧ Odd (padicValRat p (u - c)),
    p

/-- A positive `p`-adic valuation of a rational number comes from its numerator. -/
theorem dvd_num_natAbs_of_padicValRat_pos {p : ℕ} {q : ℚ} (h : 0 < padicValRat p q) :
    p ∣ q.num.natAbs := by
  rw [padicValRat_def] at h
  have h1 : padicValInt p q.num ≠ 0 := by omega
  exact padicValNat.dvd_of_ne_zero h1

/-- `contactSupport S u` is the manuscript's `M_S(u)`: a product of distinct primes, and a
prime divides it exactly when it lies outside `S` and has positive odd valuation in some
`u - c`. -/
theorem prime_dvd_contactSupport_iff {S : Finset ℕ} {u : ℚ} (hu : u ∉ contactSet) {p : ℕ}
    (hp : p.Prime) :
    p ∣ contactSupport S u ↔
      p ∉ S ∧ ∃ c ∈ contactSet, 0 < padicValRat p (u - c) ∧ Odd (padicValRat p (u - c)) := by
  classical
  have hn : (∏ c ∈ contactSet, (u - c).num.natAbs) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro c hc
    rw [Int.natAbs_ne_zero, Rat.num_ne_zero, sub_ne_zero]
    rintro rfl
    exact hu hc
  unfold contactSupport
  rw [Prime.dvd_finsetProd_iff hp.prime]
  constructor
  · rintro ⟨a, ha, hpa⟩
    rw [Finset.mem_filter] at ha
    rw [Nat.prime_dvd_prime_iff_eq hp (Nat.prime_of_mem_primeFactors ha.1)] at hpa
    subst hpa
    convert ha.2 using 0
  · rintro ⟨hS, c, hc, hpos, hodd⟩
    refine ⟨p, ?_, dvd_rfl⟩
    rw [Finset.mem_filter, Nat.mem_primeFactors]
    exact ⟨⟨hp, (dvd_num_natAbs_of_padicValRat_pos hpos).trans (Finset.dvd_prod_of_mem _ hc), hn⟩,
      hS, c, hc, hpos, hodd⟩

/-- `F₀ = 324!`. -/
noncomputable def heightF0 : ℕ := Nat.factorial 324

/-- `D = F₀ · 3^(256 F₀⁴)`. -/
noncomputable def heightD : ℕ := heightF0 * 3 ^ (256 * heightF0 ^ 4)

/-- `G₀ = 116064000000`. -/
def heightG0 : ℕ := 116064000000

/-- `E₀ = 10 (D G₀)²`. -/
noncomputable def heightE0 : ℕ := 10 * (heightD * heightG0) ^ 2

/-- `B_cm = D² 3^(21000 D²) + 1`. -/
noncomputable def heightBcm : ℕ := heightD ^ 2 * 3 ^ (21000 * heightD ^ 2) + 1

/-- `C_cm = 2 B_cm + 4096 (1028 + 5 D + 84000 D²)`. -/
noncomputable def heightCcm : ℕ := 2 * heightBcm + 4096 * (1028 + 5 * heightD + 84000 * heightD ^ 2)

/-- `Q_R = R^(R E₀)`. -/
noncomputable def heightQ (R : ℝ) : ℝ := R ^ (R * heightE0)

/-- `H₆(S; R) = 2·10¹³ · max(1, C_cm, Q_R¹⁷)`. It depends on `S` only through the
admissible range of `R`. -/
noncomputable def heightH6 (R : ℝ) : ℝ :=
  2 * 10 ^ 13 * max 1 (max (heightCcm : ℝ) (heightQ R ^ 17))

/-- **Hypothesis H** (Theorem 4.1, the six-contact estimate). For every finite set `S` of
primes containing all primes at most `324`, every `R ≥ max(D, max S, 10¹²)` and every
`u ∈ ℚ \ 𝒞`, `h(u) ≤ H₆(S; R) M_S(u)²⁴`. -/
def SixContactEstimate : Prop :=
  ∀ S : Finset ℕ, (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → p ≤ 324 → p ∈ S) →
    ∀ R : ℝ, (heightD : ℝ) ≤ R → (∀ p ∈ S, (p : ℝ) ≤ R) → (10 : ℝ) ^ 12 ≤ R →
      ∀ u : ℚ, u ∉ contactSet → ratHeight u ≤ heightH6 R * (contactSupport S u : ℝ) ^ 24

end ZInQ
