import ZInQKernel.Density.GaussSieve.Box
import ZInQKernel.Density.GaussSieve.SelbergSum

/-!
# The sieve instance of pd-paper.md §4.3 and the Selberg bound for it

For a prime `ℓ`, an integer `b`, a box size `K` and a sifting range `w ≥ 1`:

* box `ℬ = [-K, K] × [-K-1, K]`, `F(U, V) = (ℓU)² + (b + ℓV)²`;
* `P = ∏{q prime : q ≤ w, q ≡ 1 (mod 4), q ≠ ℓ}`, `ν(q) = (2q - 1)/q²`, level `w²`.

Main result `siftedSum_le`: if moreover `ℓ ≥ 5`,
`siftedSum ≤ X / S + w⁸(4K + 4)` with `X = (2K + 1)(2K + 2)` and `S ≥ (log w)/10`.
-/

open ArithmeticFunction Finset

namespace ZInQ.Density.GaussSieve

noncomputable section

open scoped Classical ArithmeticFunction.omega

/-- The sifting primes `q ≤ w`, `q ≡ 1 (mod 4)`, `q ≠ ℓ`. -/
def gsPrimes (ℓ w : ℕ) : Finset ℕ := (range (w + 1)).filter (fun q => q.Prime ∧ q % 4 = 1 ∧ q ≠ ℓ)

/-- `P = ∏_{q ∈ gsPrimes ℓ w} q`. -/
def gsProd (ℓ w : ℕ) : ℕ := ∏ q ∈ gsPrimes ℓ w, q

/-- `ν(d) = ∏_{q ∣ d} (2q - 1)/q²`. -/
def gsNu : ArithmeticFunction ℝ := prodPrimeFactors fun q => (2 * (q : ℝ) - 1) / (q : ℝ) ^ 2

/-- The box `[-K, K] × [-K-1, K]`. -/
def gsBox (K : ℕ) : Finset (ℤ × ℤ) := box (-(K : ℤ)) (-(K : ℤ) - 1) (2 * K + 1) (2 * K + 2)

/-- `F(U, V)` as a natural number. -/
def gsF (ℓ b : ℤ) (x : ℤ × ℤ) : ℕ := (gaussFZ ℓ b x).toNat

theorem gaussFZ_nonneg (ℓ b : ℤ) (x : ℤ × ℤ) : 0 ≤ gaussFZ ℓ b x := by
  unfold gaussFZ; positivity

theorem gsF_cast (ℓ b : ℤ) (x : ℤ × ℤ) : (gsF ℓ b x : ℤ) = gaussFZ ℓ b x :=
  Int.toNat_of_nonneg (gaussFZ_nonneg ℓ b x)

theorem mem_gsPrimes {ℓ w q : ℕ} :
    q ∈ gsPrimes ℓ w ↔ q ≤ w ∧ q.Prime ∧ q % 4 = 1 ∧ q ≠ ℓ := by
  simp [gsPrimes]

theorem gsProd_squarefree (ℓ w : ℕ) : Squarefree (gsProd ℓ w) :=
  Sieve.prodDistinctPrimes_squarefree _ fun _ hp => (mem_gsPrimes.1 hp).2.1

theorem mem_gsPrimes_of_dvd {ℓ w q : ℕ} (hq : q.Prime) (h : q ∣ gsProd ℓ w) : q ∈ gsPrimes ℓ w := by
  obtain ⟨r, hr, hqr⟩ := (Prime.dvd_finset_prod_iff hq.prime _).1 h
  rwa [(Nat.prime_dvd_prime_iff_eq hq (mem_gsPrimes.1 hr).2.1).1 hqr]

theorem gsNu_prime {q : ℕ} (hq : q.Prime) : gsNu q = (2 * (q : ℝ) - 1) / (q : ℝ) ^ 2 := by
  rw [gsNu, prodPrimeFactors_apply hq.ne_zero, hq.primeFactors, prod_singleton]

theorem gsNu_prime_pos {q : ℕ} (hq : q.Prime) : 0 < gsNu q := by
  rw [gsNu_prime hq]
  have : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  apply div_pos <;> nlinarith

theorem gsNu_prime_lt_one {q : ℕ} (hq : q.Prime) : gsNu q < 1 := by
  rw [gsNu_prime hq]
  have : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  rw [div_lt_one (by positivity)]
  nlinarith

/-- The sieve of pd-paper.md §4.3. -/
def gaussSieve (ℓ : ℕ) (b : ℤ) (K w : ℕ) (hw : 1 ≤ w) : SelbergSieve where
  support := (gsBox K).image (gsF ℓ b)
  prodPrimes := gsProd ℓ w
  prodPrimes_squarefree := gsProd_squarefree ℓ w
  weights n := (#((gsBox K).filter (fun x => gsF ℓ b x = n)) : ℝ)
  weights_nonneg _ := Nat.cast_nonneg _
  totalMass := (2 * K + 1) * (2 * K + 2)
  nu := gsNu
  nu_mult := IsMultiplicative.prodPrimeFactors _
  nu_pos_of_prime _ hp _ := gsNu_prime_pos hp
  nu_lt_one_of_prime _ hp _ := gsNu_prime_lt_one hp
  level := (w : ℝ) ^ 2
  one_le_level := one_le_pow₀ (by exact_mod_cast hw)

variable {ℓ : ℕ} {b : ℤ} {K w : ℕ} {hw : 1 ≤ w}

theorem multSum_eq (d : ℕ) :
    (gaussSieve ℓ b K w hw).multSum d =
      (#((gsBox K).filter (fun x => (d : ℤ) ∣ gaussFZ ℓ b x)) : ℝ) := by
  have hiff : ∀ x, (d : ℤ) ∣ gaussFZ ℓ b x ↔ d ∣ gsF ℓ b x := fun x => by
    rw [← gsF_cast, Int.natCast_dvd_natCast]
  simp_rw [hiff]
  simp only [BoundingSieve.multSum, gaussSieve]
  rw [← sum_filter]
  rw [card_eq_sum_card_fiberwise (t := ((gsBox K).image (gsF ℓ b)).filter (d ∣ ·))
    (f := gsF ℓ b) (s := (gsBox K).filter (fun x => d ∣ gsF ℓ b x))]
  · rw [Nat.cast_sum]
    refine sum_congr rfl fun n hn => ?_
    congr 2
    ext x
    simp only [mem_filter] at hn ⊢
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨h1, h2 ▸ hn.2⟩, h2⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨h1, h2⟩
  · intro x hx
    simp only [coe_filter, Set.mem_setOf_eq] at hx
    simp only [coe_filter, mem_image, Set.mem_setOf_eq]
    exact ⟨⟨x, hx.1, rfl⟩, hx.2⟩

/-- For `d ∣ P`, `#ZSet (ZMod d) = d²·ν(d)`. -/
theorem card_zset_eq_of_dvd (hℓ : ℓ.Prime) {d : ℕ} (hd : d ∣ gsProd ℓ w) :
    (Nat.card (ZSet (ZMod d) ℓ b) : ℝ) = (d : ℝ) ^ 2 * gsNu d := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd (gsProd_squarefree ℓ w)
  have hpf : ∀ q ∈ d.primeFactors, q.Prime ∧ q % 4 = 1 ∧ ¬ (q : ℤ) ∣ (ℓ : ℤ) := by
    intro q hq
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hmem := mem_gsPrimes.1 (mem_gsPrimes_of_dvd hqp ((Nat.dvd_of_mem_primeFactors hq).trans hd))
    refine ⟨hqp, hmem.2.2.1, fun h => hmem.2.2.2 ?_⟩
    rw [Int.natCast_dvd_natCast] at h
    exact (Nat.prime_dvd_prime_iff_eq hqp hℓ).1 h
  have hd_eq : d = ∏ q ∈ d.primeFactors, q := (Nat.prod_primeFactors_of_squarefree hsq).symm
  have hcard : Nat.card (ZSet (ZMod d) ℓ b) = ∏ q ∈ d.primeFactors, (2 * q - 1) := by
    have := card_zset_prod d.primeFactors hpf b
    rwa [← hd_eq] at this
  have hdR : (d : ℝ) = ∏ q ∈ d.primeFactors, (q : ℝ) := by
    rw [← Nat.cast_prod]; exact congrArg _ hd_eq
  rw [hcard, gsNu, prodPrimeFactors_apply hsq.ne_zero, hdR, Nat.cast_prod, ← prod_pow,
    ← prod_mul_distrib]
  refine prod_congr rfl fun q hq => ?_
  have hq2 : 2 ≤ q := (hpf q hq).1.two_le
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  rw [Nat.cast_sub (by omega)]
  push_cast
  field_simp

theorem card_zset_le (d : ℕ) [NeZero d] : Nat.card (ZSet (ZMod d) ℓ b) ≤ d ^ 2 := by
  rw [Nat.card_eq_fintype_card]
  refine le_trans (Fintype.card_subtype_le _) ?_
  rw [Fintype.card_prod, ZMod.card, sq]

/-- **Lemma 4.4** for the sieve: `|R_d| ≤ d²(M₁ + M₂ + 1)` for `d ∣ P`. -/
theorem abs_rem_le (hℓ : ℓ.Prime) {d : ℕ} (hd : d ∣ gsProd ℓ w) :
    |(gaussSieve ℓ b K w hw).rem d| ≤ (d : ℝ) ^ 2 * (4 * K + 4) := by
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => by
    rw [h, zero_dvd_iff] at hd; exact (gsProd_squarefree ℓ w).ne_zero hd
  have : NeZero d := ⟨hd0.ne'⟩
  have hbox := abs_card_box_dvd_sub_le (ℓ : ℤ) b (-(K : ℤ)) (-(K : ℤ) - 1) (2 * K + 1) (2 * K + 2) d hd0
  have hρ := card_zset_eq_of_dvd (b := b) hℓ hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
  simp only [BoundingSieve.rem, multSum_eq]
  have e : (gaussSieve ℓ b K w hw).nu d * (gaussSieve ℓ b K w hw).totalMass =
      (Nat.card (ZSet (ZMod d) (ℓ : ℤ) b) : ℝ) *
        (((2 * K + 1 : ℕ) : ℝ) * ((2 * K + 2 : ℕ) : ℝ) / (d : ℝ) ^ 2) := by
    simp only [gaussSieve]
    rw [hρ]; push_cast; field_simp
  rw [e]
  refine le_trans hbox ?_
  have hle : (Nat.card (ZSet (ZMod d) (ℓ : ℤ) b) : ℝ) ≤ (d : ℝ) ^ 2 := by
    exact_mod_cast card_zset_le d
  have : (((2 * K + 1 : ℕ) : ℝ) + ((2 * K + 2 : ℕ) : ℝ) + 1) = 4 * K + 4 := by push_cast; ring
  rw [this]
  exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- The Selberg terms at a sifting prime: `g(q) = (2q - 1)/(q - 1)² = (1 - 1/q)⁻² - 1`. -/
theorem selbergTerms_prime_eq {q : ℕ} (hq : q.Prime) :
    SelbergSieve.selbergTerms (gaussSieve ℓ b K w hw).toBoundingSieve q =
      1 / (1 - 1 / (q : ℝ)) ^ 2 - 1 := by
  rw [SelbergSieve.selbergTerms_apply, hq.primeFactors, prod_singleton]
  simp only [gaussSieve]
  rw [gsNu_prime hq]
  have h2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have h1 : (q : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (q : ℝ) ≠ 0 := by linarith
  have e1 : (1 : ℝ) - (2 * q - 1) / q ^ 2 = ((q : ℝ) - 1) ^ 2 / q ^ 2 := by
    field_simp; ring
  have e2 : (1 : ℝ) - 1 / q = ((q : ℝ) - 1) / q := by field_simp
  rw [e1, e2]
  field_simp
  ring

/-- `S ≥ (log w)/10` for `ℓ ≥ 5` prime. -/
theorem selbergBoundingSum_ge_log (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) :
    Real.log w / 10 ≤ (gaussSieve ℓ b K w hw).selbergBoundingSum := by
  have hS := selbergBoundingSum_ge_tau (gaussSieve ℓ b K w hw) w hw rfl fun q hq _ =>
    (selbergTerms_prime_eq hq).ge
  refine le_trans ?_ hS
  have h1 := hSum_coprime_ge hℓ w
  have h2 := log_le_hSum w
  have hℓR : (5 : ℝ) ≤ ℓ := by exact_mod_cast hℓ5
  have h35 : (3 : ℝ) / 5 ≤ 1 - 2 / ℓ := by
    rw [le_sub_iff_add_le, ← le_sub_iff_add_le', div_le_iff₀ (by positivity)]; nlinarith
  have hS0 : 0 ≤ hSum w := sum_nonneg fun n _ => hDiv_nonneg n
  have h3 : ∑ n ∈ (Ioc 0 w).filter (fun n => ¬ ℓ ∣ n), hDiv n ≤
      ∑ m ∈ (Icc 1 w).filter (fun m => (∏ p ∈ m.primeFactors, p) ∣
        (gaussSieve ℓ b K w hw).prodPrimes), tauDiv m := by
    rw [sum_filter, sum_filter]
    have hIcc : Icc 1 w = Ioc 0 w := rfl
    rw [hIcc]
    refine sum_le_sum fun n hn => ?_
    simp only [mem_Ioc] at hn
    by_cases hdiv : ℓ ∣ n
    · rw [if_neg (not_not.2 hdiv)]
      split_ifs <;> simp only [tauDiv_apply, le_refl] <;> positivity
    rw [if_pos hdiv]
    by_cases hS : AllOneMod4 n
    · have hrad : (∏ p ∈ n.primeFactors, p) ∣ (gaussSieve ℓ b K w hw).prodPrimes := by
        simp only [gaussSieve]
        refine Sieve.prod_primes_dvd_of_dvd _ (fun p hp => ?_) fun p hp => Nat.prime_of_mem_primeFactors hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpn := Nat.dvd_of_mem_primeFactors hp
        refine dvd_prod_of_mem _ (mem_gsPrimes.2 ⟨(Nat.le_of_dvd hn.1 hpn).trans hn.2, hpp,
          hS p hpp hpn, ?_⟩)
        rintro rfl; exact hdiv hpn
      rw [if_pos hrad]
      simp only [hDiv, pmul_apply, indS_apply, if_pos hS, mul_one, le_refl]
    · simp only [hDiv, pmul_apply, indS_apply, if_neg hS, mul_zero]
      split_ifs <;> simp only [tauDiv_apply, le_refl] <;> positivity
  calc Real.log w / 10 ≤ (3 / 5) * hSum w := by linarith
    _ ≤ (1 - 2 / ℓ) * hSum w := mul_le_mul_of_nonneg_right h35 hS0
    _ ≤ _ := h1
    _ ≤ _ := h3

theorem three_pow_omega_le {d : ℕ} (hd : d ∣ gsProd ℓ w) :
    (3 : ℝ) ^ (ω d) ≤ d := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd (gsProd_squarefree ℓ w)
  have hω : ω d = #d.primeFactors := by
    rw [cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]
  have hnat : 3 ^ (ω d) ≤ d := by
    rw [hω]
    conv_rhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
    refine pow_card_le_prod _ _ _ fun q hq => ?_
    have hqp := Nat.prime_of_mem_primeFactors hq
    have hmem := mem_gsPrimes.1 (mem_gsPrimes_of_dvd hqp ((Nat.dvd_of_mem_primeFactors hq).trans hd))
    have := hqp.two_le
    omega
  exact_mod_cast hnat

/-- The error term of the Selberg bound is at most `w⁸(4K + 4)`. -/
theorem errSum_le (hℓ : ℓ.Prime) :
    ∑ d ∈ (gaussSieve ℓ b K w hw).prodPrimes.divisors,
        (if (d : ℝ) ≤ (gaussSieve ℓ b K w hw).level then
          (3 : ℝ) ^ ω d * |(gaussSieve ℓ b K w hw).rem d| else 0) ≤
      (w : ℝ) ^ 8 * (4 * K + 4) := by
  have hK : (0 : ℝ) ≤ 4 * K + 4 := by positivity
  have hterm : ∀ d ∈ (gaussSieve ℓ b K w hw).prodPrimes.divisors,
      (if (d : ℝ) ≤ (gaussSieve ℓ b K w hw).level then
          (3 : ℝ) ^ ω d * |(gaussSieve ℓ b K w hw).rem d| else 0) ≤
        if d ≤ w ^ 2 then (w : ℝ) ^ 6 * (4 * K + 4) else 0 := by
    intro d hd
    have hdP : d ∣ gsProd ℓ w := Nat.dvd_of_mem_divisors hd
    simp only [gaussSieve] at hd ⊢
    by_cases h1 : (d : ℝ) ≤ (w : ℝ) ^ 2
    · have h2 : d ≤ w ^ 2 := by exact_mod_cast h1
      simp only [h1, h2, if_true]
      have h3 := three_pow_omega_le hdP
      have h4 := abs_rem_le (b := b) (K := K) (hw := hw) hℓ hdP
      simp only [gaussSieve] at h4
      calc (3 : ℝ) ^ ω d * |_| ≤ (d : ℝ) * ((d : ℝ) ^ 2 * (4 * K + 4)) :=
            mul_le_mul h3 h4 (abs_nonneg _) (Nat.cast_nonneg _)
        _ = (d : ℝ) ^ 3 * (4 * K + 4) := by ring
        _ ≤ ((w : ℝ) ^ 2) ^ 3 * (4 * K + 4) := by gcongr
        _ = (w : ℝ) ^ 6 * (4 * K + 4) := by ring
    · simp only [h1, if_false]
      split_ifs <;> positivity
  refine le_trans (sum_le_sum hterm) ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]
  have hcard : #((gaussSieve ℓ b K w hw).prodPrimes.divisors.filter (· ≤ w ^ 2)) ≤ w ^ 2 := by
    calc _ ≤ #(Icc 1 (w ^ 2)) := by
          refine card_le_card fun d hd => ?_
          simp only [mem_filter, Nat.mem_divisors] at hd
          simp only [mem_Icc]
          refine ⟨Nat.pos_of_ne_zero fun h => ?_, hd.2⟩
          rw [h, zero_dvd_iff] at hd; exact hd.1.2 hd.1.1
      _ = w ^ 2 := by simp
  calc _ ≤ ((w ^ 2 : ℕ) : ℝ) * ((w : ℝ) ^ 6 * (4 * K + 4)) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = _ := by push_cast; ring

/-- **The Selberg bound for the sieve of §4.3.** -/
theorem siftedSum_le (hℓ : ℓ.Prime) :
    (gaussSieve ℓ b K w hw).siftedSum ≤
      ((2 * K + 1) * (2 * K + 2) : ℝ) / (gaussSieve ℓ b K w hw).selbergBoundingSum +
        (w : ℝ) ^ 8 * (4 * K + 4) := by
  have h := SelbergSieve.selberg_bound_simple (gaussSieve ℓ b K w hw)
  have he := errSum_le (b := b) (K := K) (hw := hw) hℓ
  simp only [gaussSieve] at h he ⊢
  linarith

end

end ZInQ.Density.GaussSieve
