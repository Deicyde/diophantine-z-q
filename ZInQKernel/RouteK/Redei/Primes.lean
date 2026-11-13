import ZInQKernel.RouteK.Redei.Field

/-!
# Rédei's formula, step 2: primes of `ℚ(√−n)` (`docs/research/redei-plan.md` §3.2)

`K = QNeg n`, `O = 𝓞 K`, `σ` the nontrivial automorphism.

* generalities: `absNorm_span_natCast_eq` (`N(m O) = m²`), `natCast_mem_of_liesOver`,
  `intCast_mem_iff_of_liesOver`, `liesOver_of_natCast_mem`, `exists_prime_liesOver`,
  `smul_span_natCast`, `smul_eq_of_pow_le`, `eq_of_dvd_of_absNorm_eq`;
* `prime_trichotomy`: a prime `P` over `p` is split (`P σP = pO`, `N P = p`), inert (`P = pO`,
  `N P = p²`) or ramified (`P² = pO`, `N P = p`). The proof uses only norms of ideals and
  the transitivity of the Galois action on the primes over `p`
  (`Ideal.exists_smul_eq_of_isGaloisGroup`); no ramification indices;
* `dvd_of_ramified`: a ramified prime divides `n`, or is `2` with `n ≡ 1 (mod 4)` (residue field
  argument: `x − σx ∈ P`, with `x = ω` and `x = θ`);
* `ramified_of_dvd` (`p ∣ n`, `n` squarefree) and `ramified_two` (`n ≡ 1 (mod 4)`);
* `ramSet`, `ramIdeal`, `ramIdeal_spec`, `ramIdeal_mem`, `eq_ramIdeal_of_liesOver`;
* `span_omega : (√−n) = Π_{p ∣ n} 𝔭_p`;
* `mul_conj_ideal : 𝔞 σ(𝔞) = (N𝔞)`, and `absNorm_smul : N(σ𝔞) = N𝔞`.
-/

noncomputable section

open NumberField Pointwise
open scoped nonZeroDivisors

namespace ZInQ.RouteK.Redei

open ZInQ.RouteK.Rank5b

section Primes

variable (n : ℕ) [NeZero n]

local notation "K" => QNeg n
local notation "O" => 𝓞 (QNeg n)

variable {n}

/-! ### Generalities -/

theorem absNorm_span_natCast_eq (m : ℕ) : Ideal.absNorm (Ideal.span {(m : O)}) = m ^ 2 := by
  rw [Ideal.absNorm_span_natCast, finrank_int]

theorem span_natCast_isPrime {p : ℕ} (hp : p.Prime) : (Ideal.span {(p : ℤ)}).IsPrime :=
  (Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.mp hp)

theorem natCast_mem_of_liesOver {p : ℕ} (P : Ideal O) [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (p : O) ∈ P := by
  have := (Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) (p : ℤ)).1
    (Ideal.mem_span_singleton_self _)
  simpa using this

theorem span_le_of_liesOver {p : ℕ} (P : Ideal O) [P.LiesOver (Ideal.span {(p : ℤ)})] :
    Ideal.span {(p : O)} ≤ P :=
  (Ideal.span_singleton_le_iff_mem _).2 (natCast_mem_of_liesOver P)

theorem intCast_mem_iff_of_liesOver {p : ℕ} (P : Ideal O) [P.LiesOver (Ideal.span {(p : ℤ)})]
    (m : ℤ) : (m : O) ∈ P ↔ (p : ℤ) ∣ m := by
  rw [← Ideal.mem_span_singleton, Ideal.mem_of_liesOver P (Ideal.span {(p : ℤ)}) m]
  simp

theorem liesOver_of_natCast_mem {p : ℕ} (hp : p.Prime) (P : Ideal O) [P.IsPrime]
    (h : (p : O) ∈ P) : P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [Ideal.liesOver_iff]
  refine Ideal.IsMaximal.eq_of_le inferInstance Ideal.IsPrime.ne_top' ?_
  rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
  simpa using h

theorem exists_prime_liesOver (P : Ideal O) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : NeZero P := ⟨hP⟩
  exact ⟨_, Nat.absNorm_under_prime P, inferInstance⟩

theorem natCast_ne_zero_O {m : ℕ} (hm : m ≠ 0) : (m : O) ≠ 0 := by
  exact_mod_cast hm

theorem ne_bot_of_liesOver {p : ℕ} (hp : p.Prime) (P : Ideal O)
    [P.LiesOver (Ideal.span {(p : ℤ)})] : P ≠ ⊥ := by
  intro h
  have := natCast_mem_of_liesOver (p := p) P
  rw [h, Ideal.mem_bot] at this
  exact natCast_ne_zero_O hp.ne_zero this

theorem smul_natCast_O (σ : K ≃ₐ[ℚ] K) (m : ℕ) : σ • (m : O) = m := by
  apply RingOfIntegers.ext; simp

theorem smul_intCast_O (σ : K ≃ₐ[ℚ] K) (m : ℤ) : σ • (m : O) = m := by
  apply RingOfIntegers.ext; simp

theorem smul_span_natCast (σ : K ≃ₐ[ℚ] K) (m : ℕ) :
    σ • Ideal.span {(m : O)} = Ideal.span {(m : O)} := by
  rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
  congr 2
  exact smul_natCast_O σ m

theorem span_le_smul_of_liesOver (σ : K ≃ₐ[ℚ] K) {p : ℕ} (P : Ideal O)
    [P.LiesOver (Ideal.span {(p : ℤ)})] : Ideal.span {(p : O)} ≤ σ • P := by
  rw [← smul_span_natCast σ p]
  exact Ideal.pointwise_smul_le_pointwise_smul_iff.2 (span_le_of_liesOver P)

theorem smul_ne_bot (σ : K ≃ₐ[ℚ] K) {I : Ideal O} (hI : I ≠ ⊥) : σ • I ≠ ⊥ := by
  intro h
  apply hI
  have := congrArg (fun J => σ⁻¹ • J) h
  simpa using this

theorem smul_isMaximal (σ : K ≃ₐ[ℚ] K) (P : Ideal O) [P.IsMaximal] : (σ • P).IsMaximal := by
  have hP : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField inferInstance
    (RingOfIntegers.not_isField K)
  exact Ideal.IsPrime.isMaximal inferInstance (smul_ne_bot σ hP)

theorem smul_eq_of_pow_le (σ : K ≃ₐ[ℚ] K) (P : Ideal O) [P.IsMaximal] {k : ℕ}
    (h : P ^ k ≤ σ • P) : σ • P = P :=
  (Ideal.IsMaximal.eq_of_le inferInstance Ideal.IsPrime.ne_top'
    (Ideal.IsPrime.le_of_pow_le h)).symm

/-- An ideal dividing another one of the same nonzero norm is equal to it. -/
theorem eq_of_dvd_of_absNorm_eq {I J : Ideal O} (hIJ : I ∣ J) (hN : Ideal.absNorm I = Ideal.absNorm J)
    (h0 : Ideal.absNorm J ≠ 0) : I = J := by
  obtain ⟨M, rfl⟩ := hIJ
  rw [map_mul] at hN h0
  have hM : Ideal.absNorm M = 1 := by
    have h1 : Ideal.absNorm I ≠ 0 := left_ne_zero_of_mul h0
    have : Ideal.absNorm I * Ideal.absNorm M = Ideal.absNorm I * 1 := by rw [mul_one]; exact hN.symm
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h1) this
  rw [Ideal.absNorm_eq_one_iff] at hM
  rw [hM, Ideal.mul_top]

/-! ### The trichotomy -/

variable (n) in
/-- Splitting trichotomy for a prime `P` of `𝓞 K` over `p`: split, inert or ramified. -/
theorem prime_trichotomy (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) {p : ℕ} (hp : p.Prime)
    (P : Ideal O) [P.IsMaximal] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    (σ • P ≠ P ∧ P * (σ • P) = Ideal.span {(p : O)} ∧ Ideal.absNorm P = p) ∨
    (σ • P = P ∧ P = Ideal.span {(p : O)} ∧ Ideal.absNorm P = p ^ 2) ∨
    (σ • P = P ∧ P ^ 2 = Ideal.span {(p : O)} ∧ Ideal.absNorm P = p) := by
  have hle : Ideal.span {(p : O)} ≤ P := span_le_of_liesOver P
  have hles : Ideal.span {(p : O)} ≤ σ • P := span_le_smul_of_liesOver σ P
  obtain ⟨M, hM⟩ := Ideal.dvd_iff_le.2 hle
  have hN : Ideal.absNorm P * Ideal.absNorm M = p ^ 2 := by
    rw [← map_mul, ← hM, absNorm_span_natCast_eq]
  have hP1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact Ideal.IsPrime.ne_top'
  have hp0 := hp.pos
  obtain ⟨k, hk, hPk⟩ := (Nat.dvd_prime_pow hp).1 (Dvd.intro _ hN)
  interval_cases k
  · rw [pow_zero] at hPk; exact absurd hPk hP1
  · rw [pow_one] at hPk
    have hMN : Ideal.absNorm M = p := by
      rw [hPk, pow_two] at hN
      exact Nat.eq_of_mul_eq_mul_left hp0 hN
    have hMprime : M.IsPrime := Ideal.isPrime_of_irreducible_absNorm (by rw [hMN]; exact hp)
    have hMle : Ideal.span {(p : O)} ≤ M := Ideal.le_of_dvd ⟨P, by rw [hM, mul_comm]⟩
    have : M.LiesOver (Ideal.span {(p : ℤ)}) :=
      liesOver_of_natCast_mem hp M (hMle (Ideal.mem_span_singleton_self _))
    have := span_natCast_isPrime hp
    obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) P M (K ≃ₐ[ℚ] K)
    rcases eq_one_or_eq_conj σ hσ τ with h | h
    · rw [h, one_smul] at hτ
      rw [← hτ] at hM
      have hP2 : P ^ 2 = Ideal.span {(p : O)} := by rw [pow_two, hM]
      have hs : σ • P = P := smul_eq_of_pow_le σ P (k := 2) (hP2.le.trans hles)
      exact Or.inr (Or.inr ⟨hs, hP2, hPk⟩)
    · rw [h] at hτ
      by_cases hs : σ • P = P
      · refine Or.inr (Or.inr ⟨hs, ?_, hPk⟩)
        rw [pow_two, hM, ← hτ, hs]
      · exact Or.inl ⟨hs, by rw [hτ, hM], hPk⟩
  · have hM1 : Ideal.absNorm M = 1 := by
      rw [hPk] at hN
      have : p ^ 2 * Ideal.absNorm M = p ^ 2 * 1 := by rw [mul_one, hN]
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    rw [Ideal.absNorm_eq_one_iff] at hM1
    rw [hM1, Ideal.mul_top] at hM
    have hs : σ • P = P :=
      smul_eq_of_pow_le σ P (k := 1) (by rw [pow_one]; exact (le_of_eq hM.symm).trans hles)
    exact Or.inr (Or.inl ⟨hs, hM.symm, hPk⟩)

/-! ### Ramified primes divide the discriminant -/

theorem absNorm_of_ramified {p : ℕ} (P : Ideal O) (hram : P ^ 2 = Ideal.span {(p : O)}) :
    Ideal.absNorm P = p := by
  have : Ideal.absNorm P ^ 2 = p ^ 2 := by rw [← map_pow, hram, absNorm_span_natCast_eq]
  exact Nat.pow_left_injective two_ne_zero this

/-- If `N P = p` then `ℤ → O/P` is onto. -/
theorem exists_int_sub_mem_of_absNorm (P : Ideal O) [P.IsMaximal] {p : ℕ} (hp : p.Prime)
    (hN : Ideal.absNorm P = p) (x : O) : ∃ m : ℤ, x - m ∈ P := by
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card (O ⧸ P) = p := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hN]
  have : Finite (O ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  have : Fintype (O ⧸ P) := Fintype.ofFinite _
  have hc : Fintype.card (O ⧸ P) = p := by rw [← Nat.card_eq_fintype_card, hcard]
  have : CharP (O ⧸ P) p := charP_of_card_eq_prime hc
  let f : ZMod p →+* O ⧸ P := ZMod.castHom (dvd_refl p) (O ⧸ P)
  have hf : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨f.injective, by rw [ZMod.card, hc]⟩
  obtain ⟨z, hz⟩ := hf.2 (Ideal.Quotient.mk P x)
  refine ⟨(z.val : ℤ), ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hz]
  show (z.cast : O ⧸ P) - Ideal.Quotient.mk P ((z.val : ℤ) : O) = 0
  rw [map_intCast, Int.cast_natCast, ZMod.natCast_val, sub_self]

/-- If `σP = P` and `N P = p`, then `σ` acts trivially on `O/P`. -/
theorem sub_conj_mem (σ : K ≃ₐ[ℚ] K) (P : Ideal O) [P.IsMaximal] (hs : σ • P = P) {p : ℕ}
    (hp : p.Prime) (hN : Ideal.absNorm P = p) (x : O) : x - σ • x ∈ P := by
  obtain ⟨m, hm⟩ := exists_int_sub_mem_of_absNorm P hp hN x
  have h2 : σ • (x - m) ∈ P := by
    rw [← hs]; exact Ideal.smul_mem_pointwise_smul σ _ P hm
  rw [smul_sub, smul_intCast_O] at h2
  have := Ideal.sub_mem P hm h2
  convert this using 1; ring

theorem conj_thetaO (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (h3 : n % 4 = 3) :
    σ • thetaO n h3 = 1 - thetaO n h3 := by
  apply RingOfIntegers.ext
  simp only [RingOfIntegers.coe_eq_algebraMap, algebraMap_smul, algebraMap_thetaO, map_sub,
    map_one, map_div₀, map_add, map_ofNat, conj_omega σ hσ]
  ring

variable (n) in
/-- A ramified prime divides the discriminant: `p ∣ n`, or `p = 2` and `n ≡ 1 (mod 4)`. -/
theorem dvd_of_ramified {p : ℕ} (hp : p.Prime) (P : Ideal O) [P.IsMaximal]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (hram : P ^ 2 = Ideal.span {(p : O)}) :
    p ∣ n ∨ (p = 2 ∧ n % 4 = 1) := by
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := n)
  have hs : σ • P = P :=
    smul_eq_of_pow_le σ P (k := 2) (by rw [hram]; exact span_le_smul_of_liesOver σ P)
  have hN := absNorm_of_ramified P hram
  have hω := sub_conj_mem σ P hs hp hN (omegaO n)
  rw [conj_omegaO σ hσ, sub_neg_eq_add] at hω
  have h4n : ((-(4 * n : ℤ) : ℤ) : O) ∈ P := by
    have e : ((-(4 * n : ℤ) : ℤ) : O) = (omegaO n + omegaO n) * (omegaO n + omegaO n) := by
      rw [show (omegaO n + omegaO n) * (omegaO n + omegaO n) = 4 * (omegaO n * omegaO n) by ring,
        omegaO_sq]
      push_cast; ring
    rw [e]; exact Ideal.mul_mem_left P _ hω
  rw [intCast_mem_iff_of_liesOver (p := p) P, Int.dvd_neg] at h4n
  have h4n' : p ∣ 4 * n := by exact_mod_cast h4n
  rcases (Nat.Prime.dvd_mul hp).1 h4n' with h4 | hpn
  · have hp2 : p = 2 := by
      have : p ∣ 2 ^ 2 := by norm_num; exact h4
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow this)
    subst hp2
    by_cases h2n : 2 ∣ n
    · exact Or.inl h2n
    · have h3 : n % 4 = 1 ∨ n % 4 = 3 := by omega
      rcases h3 with h1 | h3
      · exact Or.inr ⟨rfl, h1⟩
      · exfalso
        have hθ := sub_conj_mem σ P hs hp hN (thetaO n h3)
        rw [conj_thetaO σ hσ h3] at hθ
        have hθ' : omegaO n ∈ P := by
          have e : thetaO n h3 - (1 - thetaO n h3) = omegaO n := by
            rw [show thetaO n h3 - (1 - thetaO n h3) = 2 * thetaO n h3 - 1 by ring,
              two_mul_thetaO]; ring
          rwa [e] at hθ
        have hn : ((-(n : ℤ) : ℤ) : O) ∈ P := by
          have e : ((-(n : ℤ) : ℤ) : O) = omegaO n * omegaO n := by rw [omegaO_sq]; push_cast; ring
          rw [e]; exact Ideal.mul_mem_left P _ hθ'
        rw [intCast_mem_iff_of_liesOver (p := 2) P, Int.dvd_neg] at hn
        exact h2n (by exact_mod_cast hn)
  · exact Or.inl hpn

/-! ### The primes of the discriminant ramify -/

/-- In the split and inert cases, `x² ∈ pO` implies `x ∈ pO`. -/
theorem mem_span_of_mul_self_mem (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) {p : ℕ} (hp : p.Prime)
    (P : Ideal O) [P.IsMaximal] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (hnr : ¬ P ^ 2 = Ideal.span {(p : O)}) {x : O} (hx : x * x ∈ Ideal.span {(p : O)}) :
    x ∈ Ideal.span {(p : O)} := by
  rcases prime_trichotomy n σ hσ hp P with ⟨hne, hmul, -⟩ | ⟨-, hP, -⟩ | ⟨-, h2, -⟩
  · have hxP : x ∈ P :=
      (Ideal.IsPrime.mem_or_mem inferInstance (span_le_of_liesOver P hx)).elim id id
    have hxs : x ∈ σ • P :=
      (Ideal.IsPrime.mem_or_mem inferInstance (span_le_smul_of_liesOver σ P hx)).elim id id
    have hmax := smul_isMaximal σ P
    have hcop : P ⊔ σ • P = ⊤ := Ideal.IsMaximal.coprime_of_ne inferInstance hmax (Ne.symm hne)
    rw [← hmul, Ideal.mul_eq_inf_of_coprime hcop]
    exact ⟨hxP, hxs⟩
  · rw [← hP] at hx ⊢
    exact (Ideal.IsPrime.mem_or_mem inferInstance hx).elim id id
  · exact absurd h2 hnr

/-- A prime `p ∣ n` (`n` squarefree) is ramified. -/
theorem ramified_of_dvd (hsq : Squarefree n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ n)
    (P : Ideal O) [P.IsMaximal] [P.LiesOver (Ideal.span {(p : ℤ)})] :
    P ^ 2 = Ideal.span {(p : O)} := by
  by_contra hnr
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := n)
  obtain ⟨c, hc⟩ := hpn
  have hcO : (n : O) = (p : O) * c := by
    have := congrArg (fun m : ℕ => (m : O)) hc; simpa using this
  have hx : omegaO n * omegaO n ∈ Ideal.span {(p : O)} := by
    rw [omegaO_sq, Ideal.mem_span_singleton]
    exact ⟨-(c : O), by rw [hcO]; ring⟩
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (mem_span_of_mul_self_mem σ hσ hp P hnr hx)
  have hN := congrArg (Algebra.norm ℤ) hy
  rw [normZ_omega, map_mul, normZ_natCast] at hN
  have : (p : ℤ) * p ∣ (n : ℤ) := ⟨Algebra.norm ℤ y, by rw [hN]; ring⟩
  have hpp : p * p ∣ n := by exact_mod_cast this
  exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p hpp))

/-- For `n ≡ 1 (mod 4)` the prime `2` is ramified. -/
theorem ramified_two (h1 : n % 4 = 1) (P : Ideal O) [P.IsMaximal]
    [P.LiesOver (Ideal.span {((2 : ℕ) : ℤ)})] :
    P ^ 2 = Ideal.span {((2 : ℕ) : O)} := by
  by_contra hnr
  obtain ⟨σ, hσ⟩ := exists_conj_ne_one (n := n)
  obtain ⟨c, hc⟩ : ∃ c : ℕ, n = 4 * c + 1 := ⟨n / 4, by omega⟩
  have hx : (1 + omegaO n) * (1 + omegaO n) ∈ Ideal.span {((2 : ℕ) : O)} := by
    rw [Ideal.mem_span_singleton]
    refine ⟨omegaO n - 2 * c, ?_⟩
    have hcO : (n : O) = 4 * c + 1 := by
      have := congrArg (fun m : ℕ => (m : O)) hc; simpa using this
    rw [show (1 + omegaO n) * (1 + omegaO n) = 1 + 2 * omegaO n + omegaO n * omegaO n by ring,
      omegaO_sq, hcO]
    push_cast; ring
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 (mem_span_of_mul_self_mem σ hσ Nat.prime_two P hnr hx)
  have hN := congrArg (Algebra.norm ℤ) hy
  rw [normZ_one_add_omega, map_mul, normZ_natCast] at hN
  omega

/-! ### The ramified primes `𝔭_p` -/

omit [NeZero n] in
variable (n) in
/-- The primes of the discriminant of `ℚ(√−n)`, `n` odd squarefree. -/
def ramSet : Finset ℕ := if n % 4 = 3 then n.primeFactors else insert 2 n.primeFactors

theorem exists_maximal_liesOver {p : ℕ} (hp : p.Prime) :
    ∃ P : Ideal O, P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
  have : Fact p.Prime := ⟨hp⟩
  exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral (Ideal.span {(p : ℤ)})

variable (n) in
/-- For `p` prime, a chosen prime of `𝓞 K` above `p` (`⊤` if `p` is not prime). For `p ∈ ramSet n`
it is the unique prime above `p`, ramified of norm `p` (`ramIdeal_spec`). -/
def ramIdeal (p : ℕ) : Ideal O :=
  if hp : p.Prime then Classical.choose (exists_maximal_liesOver (n := n) hp) else ⊤

theorem ramIdeal_isMaximal {p : ℕ} (hp : p.Prime) : (ramIdeal n p).IsMaximal := by
  rw [ramIdeal, dite_eq_left hp]
  exact (Classical.choose_spec (exists_maximal_liesOver (n := n) hp)).1

theorem ramIdeal_liesOver {p : ℕ} (hp : p.Prime) :
    (ramIdeal n p).LiesOver (Ideal.span {(p : ℤ)}) := by
  rw [ramIdeal, dite_eq_left hp]
  exact (Classical.choose_spec (exists_maximal_liesOver (n := n) hp)).2

omit [NeZero n] in
theorem prime_of_mem_ramSet {p : ℕ} (hp : p ∈ ramSet n) : p.Prime := by
  unfold ramSet at hp
  split_ifs at hp
  · exact Nat.prime_of_mem_primeFactors hp
  · rcases Finset.mem_insert.1 hp with rfl | hp
    · exact Nat.prime_two
    · exact Nat.prime_of_mem_primeFactors hp

theorem ramIdeal_sq (hn : Odd n) (hsq : Squarefree n) {p : ℕ} (hp : p ∈ ramSet n) :
    ramIdeal n p ^ 2 = Ideal.span {(p : O)} := by
  have hpp := prime_of_mem_ramSet hp
  have := ramIdeal_isMaximal (n := n) hpp
  have := ramIdeal_liesOver (n := n) hpp
  unfold ramSet at hp
  split_ifs at hp with h3
  · exact ramified_of_dvd hsq hpp (Nat.dvd_of_mem_primeFactors hp) _
  · rcases Finset.mem_insert.1 hp with rfl | hp
    · have h1 : n % 4 = 1 := by have := Nat.odd_iff.1 hn; omega
      exact ramified_two h1 _
    · exact ramified_of_dvd hsq hpp (Nat.dvd_of_mem_primeFactors hp) _

variable (n) in
theorem ramIdeal_spec (hn : Odd n) (hsq : Squarefree n) {p : ℕ} (hp : p ∈ ramSet n) :
    (ramIdeal n p).IsMaximal ∧ ramIdeal n p ^ 2 = Ideal.span {(p : O)} ∧
      Ideal.absNorm (ramIdeal n p) = p :=
  ⟨ramIdeal_isMaximal (prime_of_mem_ramSet hp), ramIdeal_sq hn hsq hp,
    absNorm_of_ramified _ (ramIdeal_sq hn hsq hp)⟩

theorem ramIdeal_ne_bot {p : ℕ} : ramIdeal n p ≠ ⊥ := by
  by_cases hp : p.Prime
  · have := ramIdeal_liesOver (n := n) hp
    exact ne_bot_of_liesOver hp _
  · rw [ramIdeal, dite_eq_right hp]; exact top_ne_bot

variable (n) in
theorem ramIdeal_mem (p : ℕ) : ramIdeal n p ∈ (Ideal O)⁰ :=
  mem_nonZeroDivisors_of_ne_zero ramIdeal_ne_bot

/-- For `p ∈ ramSet n`, `𝔭_p` is the only prime above `p`. -/
theorem eq_ramIdeal_of_liesOver (hn : Odd n) (hsq : Squarefree n) {p : ℕ} (hp : p ∈ ramSet n)
    (Q : Ideal O) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})] : Q = ramIdeal n p := by
  have := ramIdeal_isMaximal (n := n) (prime_of_mem_ramSet hp)
  have h : ramIdeal n p ^ 2 ≤ Q := by rw [ramIdeal_sq hn hsq hp]; exact span_le_of_liesOver Q
  exact (Ideal.IsMaximal.eq_of_le inferInstance Ideal.IsPrime.ne_top'
    (Ideal.IsPrime.le_of_pow_le h)).symm

theorem smul_ramIdeal (σ : K ≃ₐ[ℚ] K) (hn : Odd n) (hsq : Squarefree n) {p : ℕ}
    (hp : p ∈ ramSet n) : σ • ramIdeal n p = ramIdeal n p := by
  have := ramIdeal_isMaximal (n := n) (prime_of_mem_ramSet hp)
  have := ramIdeal_liesOver (n := n) (prime_of_mem_ramSet hp)
  exact smul_eq_of_pow_le σ _ (k := 2)
    (by rw [ramIdeal_sq hn hsq hp]; exact span_le_smul_of_liesOver σ _)

omit [NeZero n] in
theorem mem_ramSet_of_mem_primeFactors {p : ℕ} (hp : p ∈ n.primeFactors) : p ∈ ramSet n := by
  unfold ramSet; split_ifs
  · exact hp
  · exact Finset.mem_insert_of_mem hp

/-! ### `(√−n) = Π_{p ∣ n} 𝔭_p` -/

theorem omegaO_mem_ramIdeal {p : ℕ} (hp : p ∈ n.primeFactors) : omegaO n ∈ ramIdeal n p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have := ramIdeal_isMaximal (n := n) hpp
  have := ramIdeal_liesOver (n := n) hpp
  have h : omegaO n * omegaO n ∈ ramIdeal n p := by
    rw [omegaO_sq]
    obtain ⟨c, hc⟩ := Nat.dvd_of_mem_primeFactors hp
    have hcO : (n : O) = (p : O) * c := by
      have := congrArg (fun m : ℕ => (m : O)) hc; simpa using this
    rw [hcO]
    exact (Ideal.neg_mem_iff _).2 (Ideal.mul_mem_right _ _ (natCast_mem_of_liesOver _))
  exact (Ideal.IsPrime.mem_or_mem inferInstance h).elim id id

variable (n) in
/-- `(√−n) = Π_{p ∣ n} 𝔭_p`. -/
theorem span_omega (hn : Odd n) (hsq : Squarefree n) :
    Ideal.span {(⟨QuadraticAlgebra.omega, isIntegral_omega n⟩ : O)} =
      ∏ p ∈ n.primeFactors, ramIdeal n p := by
  change Ideal.span {omegaO n} = _
  symm
  refine eq_of_dvd_of_absNorm_eq ?_ ?_ ?_
  · refine Finset.prod_dvd_of_coprime ?_ fun p hp => ?_
    · intro p hp q hq hpq
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hqp := Nat.prime_of_mem_primeFactors hq
      have := ramIdeal_isMaximal (n := n) hpp
      have := ramIdeal_isMaximal (n := n) hqp
      have := ramIdeal_liesOver (n := n) hpp
      have := ramIdeal_liesOver (n := n) hqp
      rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
      refine Ideal.IsMaximal.coprime_of_ne inferInstance inferInstance fun h => hpq ?_
      have hq' : ((q : ℤ) : O) ∈ ramIdeal n p := by
        rw [h]; simpa using natCast_mem_of_liesOver (p := q) (ramIdeal n q)
      rw [intCast_mem_iff_of_liesOver (p := p) (ramIdeal n p)] at hq'
      exact (Nat.prime_dvd_prime_iff_eq hpp hqp).1 (by exact_mod_cast hq')
    · rw [Ideal.dvd_span_singleton]
      exact omegaO_mem_ramIdeal (n := n) hp
  · rw [map_prod, Ideal.absNorm_span_singleton]
    have : ∀ p ∈ n.primeFactors, Ideal.absNorm (ramIdeal n p) = p := fun p hp =>
      (ramIdeal_spec n hn hsq (mem_ramSet_of_mem_primeFactors hp)).2.2
    rw [Finset.prod_congr rfl this, Nat.prod_primeFactors_of_squarefree hsq]
    have := normZ_omega (n := n)
    simp only [omegaO] at this
    rw [this]; simp
  · rw [Ideal.absNorm_span_singleton]
    have := normZ_omega (n := n)
    simp only [omegaO] at this
    rw [this]; simpa using NeZero.ne n

/-! ### `𝔞 σ(𝔞) = (N𝔞)` -/

theorem mul_conj_prime (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (P : Ideal O) [P.IsPrime] (hP : P ≠ ⊥) :
    P * (σ • P) = Ideal.span {((Ideal.absNorm P : ℕ) : O)} := by
  have := Ideal.IsPrime.isMaximal inferInstance hP
  obtain ⟨p, hp, hlies⟩ := exists_prime_liesOver P hP
  rcases prime_trichotomy n σ hσ hp P with ⟨-, hmul, hN⟩ | ⟨hs, hP', hN⟩ | ⟨hs, h2, hN⟩
  · rw [hN, hmul]
  · rw [hs, hN, Nat.cast_pow, pow_two, ← Ideal.span_singleton_mul_span_singleton, ← hP']
  · rw [hs, hN, ← pow_two, h2]

variable (n) in
/-- `𝔞 σ(𝔞) = (N𝔞)`. -/
theorem mul_conj_ideal (σ : K ≃ₐ[ℚ] K) (hσ : σ ≠ 1) (I : Ideal O) :
    I * (σ • I) = Ideal.span {((Ideal.absNorm I : ℕ) : O)} := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ =>
    rw [Ideal.zero_eq_bot, Ideal.absNorm_bot, Nat.cast_zero, Ideal.span_singleton_eq_bot.2 rfl,
      Ideal.bot_mul]
  | h₂ x hx =>
    rw [Ideal.isUnit_iff] at hx
    subst hx
    rw [← Ideal.one_eq_top, smul_one, one_mul, map_one, Nat.cast_one, Ideal.span_singleton_one,
      Ideal.one_eq_top]
  | h₃ a P ha hP ih =>
    have hP0 : P ≠ ⊥ := hP.ne_zero
    have := Ideal.isPrime_of_prime hP
    rw [smul_mul', map_mul, Nat.cast_mul, ← Ideal.span_singleton_mul_span_singleton, ← ih,
      ← mul_conj_prime σ hσ P hP0]
    ring

variable (n) in
/-- `N(σ𝔞) = N𝔞`. -/
theorem absNorm_smul (σ : K ≃ₐ[ℚ] K) (I : Ideal O) :
    Ideal.absNorm (σ • I) = Ideal.absNorm I := by
  by_cases hσ : σ = 1
  · rw [hσ, one_smul]
  by_cases hI : Ideal.absNorm I = 0
  · rw [hI, Ideal.absNorm_eq_zero_iff.1 hI]
    have : σ • (⊥ : Ideal O) = ⊥ := by rw [← Ideal.zero_eq_bot, smul_zero]
    rw [this, Ideal.absNorm_bot]
  · have h := congrArg Ideal.absNorm (mul_conj_ideal n σ hσ I)
    rw [map_mul, absNorm_span_natCast_eq, pow_two] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hI) h

end Primes

end ZInQ.RouteK.Redei
