import ZInQKernel.Progressions.IdealCount.Basic

/-!
# Ideal counts at prime powers

For a prime `p`, an ideal of `𝓞 K` of norm `p ^ k` is a product `∏ P ^ a P` over the primes `P`
above `p`, with `∑ a P * f P = k` where `p ^ f P` is the norm of `P`; unique factorization makes
this a bijection (`IdealCount.primePowEquiv`). Applied to `(p)` itself, of norm `p ^ [K : ℚ]`, it
gives `∑ e P * f P = [K : ℚ]`. For a quadratic field this leaves three cases (one prime of
degree 2, one prime of degree 1, two primes of degree 1), whence
`idealCount K (p ^ k) = ∑ j ≤ k, ε ^ j` with `ε = idealCount K p - 1 ∈ {-1, 0, 1}`
(plan step 3.3, item 2).
-/

namespace ZInQ.Progressions

open NumberField Ideal UniqueFactorizationMonoid Module

open Classical

variable {K : Type*} [Field K] [NumberField K]

namespace IdealCount

/-- The prime ideals of `𝓞 K` above `p`. -/
noncomputable def primesOver (K : Type*) [Field K] [NumberField K] (p : ℕ) :
    Finset (Ideal (𝓞 K)) :=
  (normalizedFactors (span {(p : 𝓞 K)})).toFinset

/-- The residue degree of `P` over `p`: the exponent of `p` in the norm of `P`. -/
noncomputable def resDeg (p : ℕ) (P : Ideal (𝓞 K)) : ℕ :=
  (absNorm P).factorization p

variable {p : ℕ}

theorem span_natCast_ne_bot (hp : p.Prime) : span {(p : 𝓞 K)} ≠ ⊥ := by
  rw [Ne, span_singleton_eq_bot]
  exact_mod_cast hp.ne_zero

theorem mem_primesOver (hp : p.Prime) {P : Ideal (𝓞 K)} :
    P ∈ primesOver K p ↔ P.IsPrime ∧ (p : 𝓞 K) ∈ P := by
  rw [primesOver, Multiset.mem_toFinset, Ideal.mem_normalizedFactors_iff (span_natCast_ne_bot hp),
    span_singleton_le_iff_mem]

theorem absNorm_of_mem_primesOver (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ primesOver K p) :
    absNorm P = p ^ resDeg p P := by
  have hdvd : absNorm P ∣ p ^ finrank ℤ (𝓞 K) := by
    rw [← absNorm_span_natCast]
    exact absNorm_dvd_absNorm_of_le ((span_singleton_le_iff_mem P).mpr ((mem_primesOver hp).mp hP).2)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  rw [resDeg, hj, Nat.factorization_pow, Finsupp.smul_apply, hp.factorization_self, smul_eq_mul,
    mul_one]

theorem resDeg_pos (hp : p.Prime) {P : Ideal (𝓞 K)} (hP : P ∈ primesOver K p) :
    0 < resDeg p P := by
  refine Nat.pos_of_ne_zero fun h ↦ ((mem_primesOver hp).mp hP).1.ne_top ?_
  rw [← absNorm_eq_one_iff, absNorm_of_mem_primesOver hp hP, h, pow_zero]

theorem ne_bot_of_absNorm_eq (hp : p.Prime) {I : Ideal (𝓞 K)} {k : ℕ} (hI : absNorm I = p ^ k) :
    I ≠ ⊥ := by
  rintro rfl
  rw [absNorm_bot] at hI
  exact pow_ne_zero k hp.ne_zero hI.symm

theorem normalizedFactors_subset (hp : p.Prime) {I : Ideal (𝓞 K)} {k : ℕ}
    (hI : absNorm I = p ^ k) : (normalizedFactors I).toFinset ⊆ primesOver K p := by
  intro Q hQ
  rw [Multiset.mem_toFinset] at hQ
  obtain ⟨hQp, hIQ⟩ := (Ideal.mem_normalizedFactors_iff (ne_bot_of_absNorm_eq hp hI)).mp hQ
  have hmem : (p : 𝓞 K) ^ k ∈ Q := by
    have := absNorm_mem I
    rw [hI] at this
    exact hIQ (by exact_mod_cast this)
  exact (mem_primesOver hp).mpr ⟨hQp, hQp.mem_of_pow_mem k hmem⟩

theorem absNorm_prod (hp : p.Prime) (a : Ideal (𝓞 K) → ℕ) :
    absNorm (∏ Q ∈ primesOver K p, Q ^ a Q) = p ^ ∑ Q ∈ primesOver K p, a Q * resDeg p Q := by
  rw [map_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun Q hQ ↦ ?_
  rw [map_pow, absNorm_of_mem_primesOver hp hQ, ← pow_mul, mul_comm]

theorem prod_count_eq (hp : p.Prime) {I : Ideal (𝓞 K)} {k : ℕ} (hI : absNorm I = p ^ k) :
    ∏ Q ∈ primesOver K p, Q ^ (normalizedFactors I).count Q = I := by
  rw [← Finset.prod_multiset_count_of_subset _ _ (normalizedFactors_subset hp hI),
    Ideal.prod_normalizedFactors_eq_self (ne_bot_of_absNorm_eq hp hI)]

theorem count_prod_eq (a : Ideal (𝓞 K) → ℕ) (Q : Ideal (𝓞 K)) :
    (normalizedFactors (∏ Q' ∈ primesOver K p, Q' ^ a Q')).count Q =
      if Q ∈ primesOver K p then a Q else 0 := by
  set M : Multiset (Ideal (𝓞 K)) := ∑ Q' ∈ primesOver K p, Multiset.replicate (a Q') Q'
  have hcount : ∀ Q, M.count Q = if Q ∈ primesOver K p then a Q else 0 := by
    intro Q
    simp only [M, Multiset.count_sum', Multiset.count_replicate, Finset.sum_ite_eq']
  have hsub : M.toFinset ⊆ primesOver K p := by
    intro Q hQ
    rw [Multiset.mem_toFinset, ← Multiset.count_pos, hcount] at hQ
    split_ifs at hQ with h
    · exact h
    · omega
  have hprod : M.prod = ∏ Q' ∈ primesOver K p, Q' ^ a Q' := by
    rw [Finset.prod_multiset_count_of_subset _ _ hsub]
    exact Finset.prod_congr rfl fun Q hQ ↦ by simp [hcount, hQ]
  have hprime : ∀ Q ∈ M, Prime Q := fun Q hQ ↦
    prime_of_normalized_factor Q (Multiset.mem_toFinset.mp (hsub (Multiset.mem_toFinset.mpr hQ)))
  rw [← hprod, normalizedFactors_prod_of_prime hprime, hcount]

/-- Ideals of norm `p ^ k` are the products `∏ P ^ a P` over the primes above `p` with
`∑ a P * f P = k`. -/
noncomputable def primePowEquiv (hp : p.Prime) (k : ℕ) :
    {I : Ideal (𝓞 K) // absNorm I = p ^ k} ≃
      {a : Ideal (𝓞 K) → ℕ // (∀ Q ∉ primesOver K p, a Q = 0) ∧
        ∑ Q ∈ primesOver K p, a Q * resDeg p Q = k} where
  toFun I := ⟨fun Q ↦ (normalizedFactors I.1).count Q,
    fun Q hQ ↦ Multiset.count_eq_zero.mpr fun h ↦
      hQ (normalizedFactors_subset hp I.2 (Multiset.mem_toFinset.mpr h)), by
      have := absNorm_prod hp (fun Q ↦ (normalizedFactors I.1).count Q)
      rw [prod_count_eq hp I.2, I.2] at this
      exact (Nat.pow_right_injective hp.two_le this).symm⟩
  invFun a := ⟨∏ Q ∈ primesOver K p, Q ^ a.1 Q, by rw [absNorm_prod hp, a.2.2]⟩
  left_inv I := Subtype.ext (prod_count_eq hp I.2)
  right_inv a := by
    refine Subtype.ext (funext fun Q ↦ ?_)
    change (normalizedFactors (∏ Q' ∈ primesOver K p, Q' ^ a.1 Q')).count Q = a.1 Q
    rw [count_prod_eq]
    split_ifs with h
    · rfl
    · exact (a.2.1 Q h).symm

theorem idealCount_pow_eq_card (hp : p.Prime) (k : ℕ) :
    idealCount K (p ^ k) = Nat.card {a : Ideal (𝓞 K) → ℕ // (∀ Q ∉ primesOver K p, a Q = 0) ∧
        ∑ Q ∈ primesOver K p, a Q * resDeg p Q = k} :=
  Nat.card_congr (primePowEquiv hp k)

/-- `∑ e P * f P = [K : ℚ]`, with `e P` the multiplicity of `P` in `(p)`. -/
theorem sum_count_mul_resDeg (hp : p.Prime) :
    ∑ Q ∈ primesOver K p, (normalizedFactors (span {(p : 𝓞 K)})).count Q * resDeg p Q =
      finrank ℚ K := by
  have h : absNorm (span {(p : 𝓞 K)}) = p ^ finrank ℚ K := by
    rw [absNorm_span_natCast, RingOfIntegers.rank]
  exact ((primePowEquiv hp _) ⟨_, h⟩).2.2

theorem sum_resDeg_le (hp : p.Prime) :
    ∑ Q ∈ primesOver K p, resDeg p Q ≤ finrank ℚ K := by
  rw [← sum_count_mul_resDeg hp]
  refine Finset.sum_le_sum fun Q hQ ↦ Nat.le_mul_of_pos_left _ ?_
  exact Multiset.count_pos.mpr (Multiset.mem_toFinset.mp hQ)

theorem primesOver_nonempty (hp : p.Prime) : (primesOver K p).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro h
  have := sum_count_mul_resDeg (K := K) hp
  rw [h, Finset.sum_empty] at this
  exact Module.finrank_pos.ne this

section count

variable {α : Type*} [DecidableEq α]

theorem card_single (P : α) (f : α → ℕ) (k : ℕ) :
    Nat.card {a : α → ℕ // (∀ Q ∉ ({P} : Finset α), a Q = 0) ∧
      ∑ Q ∈ ({P} : Finset α), a Q * f Q = k} = Nat.card {n : ℕ // n * f P = k} := by
  refine Nat.card_congr
    { toFun := fun a ↦ ⟨a.1 P, by simpa using a.2.2⟩
      invFun := fun n ↦ ⟨fun Q ↦ if Q = P then n.1 else 0, fun Q hQ ↦ by
        simp only [Finset.mem_singleton] at hQ; simp [hQ], by simpa using n.2⟩
      left_inv := fun a ↦ Subtype.ext (funext fun Q ↦ by
        by_cases h : Q = P
        · subst h; simp
        · simpa [h] using (a.2.1 Q (by simpa using h)).symm)
      right_inv := fun n ↦ by simp }

theorem card_pair {P Q : α} (hPQ : P ≠ Q) (f : α → ℕ) (hP : f P = 1) (hQ : f Q = 1) (k : ℕ) :
    Nat.card {a : α → ℕ // (∀ R ∉ ({P, Q} : Finset α), a R = 0) ∧
      ∑ R ∈ ({P, Q} : Finset α), a R * f R = k} = k + 1 := by
  rw [← Finset.Nat.card_antidiagonal k, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr
    { toFun := fun a ↦ ⟨(a.1 P, a.1 Q), Finset.mem_antidiagonal.mpr (by
        simpa [Finset.sum_pair hPQ, hP, hQ] using a.2.2)⟩
      invFun := fun x ↦ ⟨fun R ↦ if R = P then x.1.1 else if R = Q then x.1.2 else 0,
        fun R hR ↦ by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hR
          simp [hR.1, hR.2], by
          simpa [Finset.sum_pair hPQ, hP, hQ, Ne.symm hPQ] using
            Finset.mem_antidiagonal.mp x.2⟩
      left_inv := fun a ↦ Subtype.ext (funext fun R ↦ by
        by_cases h1 : R = P
        · subst h1; simp
        · by_cases h2 : R = Q
          · subst h2; simp [h1]
          · simpa [h1, h2] using (a.2.1 R (by simp [h1, h2])).symm)
      right_inv := fun x ↦ by ext; simp }

end count

theorem card_mul_one (k : ℕ) : Nat.card {n : ℕ // n * 1 = k} = 1 :=
  Nat.card_eq_one_iff_exists.mpr ⟨⟨k, mul_one k⟩, fun n ↦ Subtype.ext (by simpa using n.2)⟩

theorem card_mul_two (k : ℕ) : Nat.card {n : ℕ // n * 2 = k} = if Even k then 1 else 0 := by
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    exact Nat.card_eq_one_iff_exists.mpr ⟨⟨m, by ring⟩, fun n ↦ Subtype.ext (show n.1 = m by have := n.2; omega)⟩
  · rw [Nat.card_eq_zero]
    left
    exact ⟨fun n ↦ h ⟨n.1, by have := n.2; omega⟩⟩

end IdealCount

open IdealCount

/-- The three splitting types of a prime in a quadratic field, read off from the ideal counts:
inert, ramified, split. -/
theorem idealCount_prime_pow_cases (h2 : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) :
    (∀ k, idealCount K (p ^ k) = if Even k then 1 else 0) ∨
      (∀ k, idealCount K (p ^ k) = 1) ∨ (∀ k, idealCount K (p ^ k) = k + 1) := by
  have hsum := sum_resDeg_le (K := K) hp
  rw [h2] at hsum
  have hcard : (primesOver K p).card ≤ 2 := by
    refine le_trans ?_ hsum
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun Q hQ ↦ resDeg_pos hp hQ
  obtain ⟨P, hP⟩ := primesOver_nonempty (K := K) hp
  have hcard1 : 1 ≤ (primesOver K p).card := Finset.card_pos.mpr ⟨P, hP⟩
  rcases (show (primesOver K p).card = 1 ∨ (primesOver K p).card = 2 by omega) with h | h
  · obtain ⟨P, hS⟩ := Finset.card_eq_one.mp h
    have hP := resDeg_pos hp (hS ▸ Finset.mem_singleton_self P : P ∈ primesOver K p)
    rw [hS, Finset.sum_singleton] at hsum
    rcases (show resDeg p P = 1 ∨ resDeg p P = 2 by omega) with hf | hf
    · right; left
      intro k
      rw [idealCount_pow_eq_card hp, hS, card_single, hf, card_mul_one]
    · left
      intro k
      rw [idealCount_pow_eq_card hp, hS, card_single, hf, card_mul_two]
  · obtain ⟨P, Q, hPQ, hS⟩ := Finset.card_eq_two.mp h
    have hP := resDeg_pos hp (hS ▸ Finset.mem_insert_self P {Q} : P ∈ primesOver K p)
    have hQ := resDeg_pos hp (hS ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self Q) :
      Q ∈ primesOver K p)
    rw [hS, Finset.sum_pair hPQ] at hsum
    right; right
    intro k
    rw [idealCount_pow_eq_card hp, hS, card_pair hPQ _ (by omega) (by omega)]

variable (K) in
/-- The local factor `ε_p = a_K(p) - 1` of a quadratic field at a prime `p`. -/
noncomputable def localEps (p : ℕ) : ℤ := idealCount K p - 1

/-- **Quadratic local factors** (plan step 3.3, item 2): `ε_p ∈ {-1, 0, 1}` and
`a_K(p ^ k) = ∑_{j ≤ k} ε_p ^ j`. -/
theorem localEps_mem_and_idealCount_prime_pow (h2 : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) :
    (localEps K p = -1 ∨ localEps K p = 0 ∨ localEps K p = 1) ∧
      ∀ k, (idealCount K (p ^ k) : ℤ) = ∑ j ∈ Finset.range (k + 1), localEps K p ^ j := by
  rcases idealCount_prime_pow_cases h2 hp with h | h | h
  · have he : localEps K p = -1 := by have := h 1; rw [pow_one] at this; simp [localEps, this]
    refine ⟨Or.inl he, fun k ↦ ?_⟩
    rw [he, h k, neg_one_geom_sum]
    split_ifs with h' h'' h'' <;> simp_all [Nat.even_add_one]
  · have he : localEps K p = 0 := by have := h 1; rw [pow_one] at this; simp [localEps, this]
    refine ⟨Or.inr (Or.inl he), fun k ↦ ?_⟩
    rw [he, h k, Finset.sum_range_succ']
    simp
  · have he : localEps K p = 1 := by have := h 1; rw [pow_one] at this; simp [localEps, this]
    refine ⟨Or.inr (Or.inr he), fun k ↦ ?_⟩
    rw [he, h k]
    simp

theorem localEps_mem (h2 : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) :
    localEps K p = -1 ∨ localEps K p = 0 ∨ localEps K p = 1 :=
  (localEps_mem_and_idealCount_prime_pow h2 hp).1

theorem idealCount_prime_pow (h2 : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (idealCount K (p ^ k) : ℤ) = ∑ j ∈ Finset.range (k + 1), localEps K p ^ j :=
  (localEps_mem_and_idealCount_prime_pow h2 hp).2 k

/-- Item 2 of plan step 3.3 in its existential form. -/
theorem exists_localFactor (h2 : finrank ℚ K = 2) {p : ℕ} (hp : p.Prime) :
    ∃ ε : ℤ, (ε = -1 ∨ ε = 0 ∨ ε = 1) ∧
      ∀ k, (idealCount K (p ^ k) : ℤ) = ∑ j ∈ Finset.range (k + 1), ε ^ j :=
  ⟨localEps K p, localEps_mem_and_idealCount_prime_pow h2 hp⟩

/-- The `ε` of item 2 is unique: it is `localEps K p = a_K(p) - 1`. -/
theorem eq_localEps_of_idealCount_prime_pow {p : ℕ} {ε : ℤ}
    (h : ∀ k, (idealCount K (p ^ k) : ℤ) = ∑ j ∈ Finset.range (k + 1), ε ^ j) :
    ε = localEps K p := by
  have h1 := h 1
  rw [pow_one, Finset.sum_range_succ, Finset.sum_range_one, pow_zero, pow_one] at h1
  rw [localEps, h1]
  ring

end ZInQ.Progressions
