import ZInQKernel.Contrib.GZTheta.ALRep

/-!
# atkin-li: the arithmetic of the Fricke identity

Task atkin-li. Pure arithmetic about coefficient sequences, the last step of the Atkin–Li
argument. `b` is the coefficient sequence of a newform of level `M'` (weight 2, trivial
nebentypus), `H` that of a form of level `N` (`M' ∣ N`, `P = N/M'`) with
`H = ∑_{e ∣ P} c_e b(·/e)` and the Fricke identity `κ H = c_g ∑_{e ∣ P} c_e (P/e)² b(·/(P/e))`,
`κ ≠ 0`. If `H(p^j) = 0` (`j ≥ 1`) at every prime `p ∣ P`, `v_p(N) = 2` there, then `P = 1`
(`level_eq_of_reps`).

Proof: `ν`, the multiplicative function with local factors `1 − b_p X + [p ∤ M'] p X²`, is the
Dirichlet inverse of `b`, so `c = H ⋆ ν` is multiplicative and `c(p^j) = ν(p^j)` at `p ∣ P`. The
Fricke identity gives `κ c_f = c_g c_{P/f} f²` (`f ∣ P`), hence `c(p^v)² = p^{2v}`, `v = v_p(P)`:
for `v = 2`, `c(p²) = p`; for `v = 1`, `c(p)² = b_p² = 1` (`p ∥ M'`); both contradict.
-/

open ArithmeticFunction

noncomputable section

namespace ZInQ.GZTheta

/-- The coefficients of `g(eτ)`, for a coefficient sequence `b`. -/
def Bs (b : ℕ → ℂ) (e n : ℕ) : ℂ := if e ∣ n then b (n / e) else 0

/-! ### The Dirichlet inverse of a newform's coefficients -/

/-- The local factor `1 − b_p X + [p ∤ M'] p X²`. -/
def locN (M' : ℕ) (b : ℕ → ℂ) (p j : ℕ) : ℂ :=
  if j = 0 then 1 else if j = 1 then -b p else if j = 2 ∧ ¬ p ∣ M' then (p : ℂ) else 0

/-- The multiplicative function with local factors `locN`. -/
def nuAr (M' : ℕ) (b : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod (locN M' b), by simp⟩

theorem nuAr_apply {M' : ℕ} {b : ℕ → ℂ} {n : ℕ} (hn : n ≠ 0) :
    nuAr M' b n = n.factorization.prod (locN M' b) := by
  show (if n = 0 then 0 else _) = _
  rw [if_neg hn]

theorem nuAr_mult (M' : ℕ) (b : ℕ → ℂ) : (nuAr M' b).IsMultiplicative := by
  refine ⟨by rw [nuAr_apply one_ne_zero]; simp, fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [nuAr_apply (mul_ne_zero hm hn), nuAr_apply hm, nuAr_apply hn,
    Nat.factorization_mul_of_coprime hmn]
  refine Finsupp.prod_add_index_of_disjoint ?_ _
  rw [Nat.support_factorization, Nat.support_factorization]
  exact hmn.disjoint_primeFactors

theorem nuAr_prime_pow {M' : ℕ} {b : ℕ → ℂ} {p : ℕ} (hp : p.Prime) (j : ℕ) :
    nuAr M' b (p ^ j) = locN M' b p j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, nuAr_apply one_ne_zero]; simp [locN]
  rw [nuAr_apply (pow_ne_zero _ hp.ne_zero), hp.factorization_pow, Finsupp.prod_single_index]
  simp [locN]

/-- A sequence as an arithmetic function (its value at `0` is dropped). -/
def toAr (b : ℕ → ℂ) : ArithmeticFunction ℂ := ⟨fun n => if n = 0 then 0 else b n, by simp⟩

theorem toAr_apply {b : ℕ → ℂ} {n : ℕ} (hn : n ≠ 0) : toAr b n = b n := by
  show (if n = 0 then 0 else b n) = b n
  rw [if_neg hn]

theorem toAr_mult {b : ℕ → ℂ} (h1 : b 1 = 1)
    (hmul : ∀ u v : ℕ, Nat.Coprime u v → b (u * v) = b u * b v) : (toAr b).IsMultiplicative := by
  refine ⟨by rw [toAr_apply one_ne_zero, h1], fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [toAr]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [toAr]
  rw [toAr_apply (mul_ne_zero hm hn), toAr_apply hm, toAr_apply hn, hmul m n hmn]

section Inverse

variable {M' : ℕ} {b : ℕ → ℂ} (h1 : b 1 = 1)
  (hmul : ∀ u v : ℕ, Nat.Coprime u v → b (u * v) = b u * b v)
  (hpow : ∀ (p : ℕ), p.Prime → ∀ r : ℕ, b (p ^ (r + 2)) =
      b p * b (p ^ (r + 1)) - (if p ∣ M' then 0 else (p : ℂ)) * b (p ^ r))
include h1 hmul hpow

/-- **`ν ⋆ b = 1`.** -/
theorem nuAr_mul_toAr : nuAr M' b * toAr b = 1 := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ ((nuAr_mult M' b).mul (toAr_mult h1 hmul))
    _ isMultiplicative_one).mpr fun p i hp => ?_
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun x y => nuAr M' b x * toAr b y), Nat.sum_divisors_prime_pow hp]
  simp only [nuAr_prime_pow hp]
  have hsub : ∀ k ∈ Finset.range (i + 1), p ^ i / p ^ k = p ^ (i - k) := fun k hk =>
    Nat.pow_div (by simpa [Nat.lt_succ_iff] using hk) hp.pos
  rw [Finset.sum_congr rfl fun k hk => by rw [hsub k hk, toAr_apply (pow_ne_zero _ hp.ne_zero)]]
  match i with
  | 0 => simp [locN, h1]
  | 1 =>
    simp [Finset.sum_range_succ, locN, h1, ArithmeticFunction.one_apply_ne hp.one_lt.ne']
  | r + 2 =>
    rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
    have hz : ∀ k ∈ Finset.range r, locN M' b p (k + 1 + 1 + 1) *
        b (p ^ (r + 2 - (k + 1 + 1 + 1))) = 0 := fun k _ => by simp [locN]
    rw [Finset.sum_eq_zero hz]
    have hne : p ^ (r + 2) ≠ 1 := by
      have := Nat.one_lt_pow (by omega : r + 2 ≠ 0) hp.one_lt; omega
    rw [ArithmeticFunction.one_apply_ne hne]
    simp only [locN]
    norm_num
    rw [hpow p hp r]
    by_cases hpM : p ∣ M'
    · simp [hpM]
    · simp [hpM]; ring

end Inverse

/-! ### Uniqueness of the coefficients `c` -/

theorem eq_zero_of_sum_Bs {b : ℕ → ℂ} (h1 : b 1 = 1) {P : ℕ} (hP : P ≠ 0) {x : ℕ → ℂ}
    (hx : ∀ n, ∑ e ∈ P.divisors, x e * Bs b e n = 0) : ∀ e ∈ P.divisors, x e = 0 := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he
    have h := hx e
    rw [Finset.sum_eq_single e] at h
    · simpa [Bs, Nat.div_self (Nat.pos_of_mem_divisors he), h1] using h
    · intro e' he' hne
      by_cases hd : e' ∣ e
      · have hlt : e' < e := lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_mem_divisors he) hd) hne
        rw [ih e' hlt he', zero_mul]
      · simp [Bs, hd]
    · intro h'; exact absurd he h'

/-- From `H = ∑_{e ∣ P} c_e b(·/e)`: `H = c̄ ⋆ b` with `c̄ = c` on the divisors of `P`. -/
def cbar (P : ℕ) (c : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ∣ P ∧ n ≠ 0 then c n else 0, by simp⟩

theorem cbar_apply_of_dvd {P : ℕ} {c : ℕ → ℂ} {n : ℕ} (hn : n ∈ P.divisors) :
    cbar P c n = c n := by
  show (if n ∣ P ∧ n ≠ 0 then c n else 0) = c n
  rw [if_pos ⟨Nat.dvd_of_mem_divisors hn, (Nat.pos_of_mem_divisors hn).ne'⟩]

theorem toAr_eq_cbar_mul {b H : ℕ → ℂ} {P : ℕ} (hP : P ≠ 0) {c : ℕ → ℂ}
    (hrep : ∀ n, H n = ∑ e ∈ P.divisors, c e * Bs b e n) : toAr H = cbar P c * toAr b := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [toAr]
  rw [toAr_apply hn, hrep n, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => cbar P c x * toAr b y)]
  rw [← Finset.sum_filter_add_sum_filter_not n.divisors (· ∣ P)]
  rw [Finset.sum_eq_zero (s := n.divisors.filter (fun x => ¬ x ∣ P)) (fun x hx => by
    simp only [Finset.mem_filter] at hx
    show (if x ∣ P ∧ x ≠ 0 then c x else 0) * _ = 0
    rw [if_neg (fun h => hx.2 h.1), zero_mul]), add_zero]
  rw [← Finset.sum_filter_add_sum_filter_not P.divisors (· ∣ n)]
  rw [Finset.sum_eq_zero (s := P.divisors.filter (fun x => ¬ x ∣ n)) (fun x hx => by
    simp only [Finset.mem_filter] at hx
    simp [Bs, hx.2]), add_zero]
  apply Finset.sum_congr
  · ext e
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, hn⟩, h1⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, hP⟩, h1⟩
  · intro e he
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    have he0 : e ≠ 0 := fun h0 => by rw [h0] at he; exact hn (zero_dvd_iff.mp he.1.1)
    rw [cbar_apply_of_dvd (Nat.mem_divisors.mpr ⟨he.2, hP⟩), Bs, if_pos he.1.1,
      toAr_apply (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) he.1.1)
        (Nat.pos_of_ne_zero he0)).ne']

/-! ### The level -/

/-- **`P = 1`** from the representation and the Fricke identity. -/
theorem level_eq_of_reps {N M' r : ℕ} (hN : N ≠ 0) (hM'N : M' ∣ N) {b H c : ℕ → ℂ} {κ cg : ℂ}
    (hb1 : b 1 = 1) (hbmul : ∀ u v : ℕ, Nat.Coprime u v → b (u * v) = b u * b v)
    (hbpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ, b (p ^ (j + 2)) =
      b p * b (p ^ (j + 1)) - (if p ∣ M' then 0 else (p : ℂ)) * b (p ^ j))
    (hbex : ∀ p : ℕ, p.Prime → p ∣ M' → ¬ p ^ 2 ∣ M' → b p ^ 2 = 1)
    (hH1 : H 1 = 1) (hHmul : ∀ u v : ℕ, Nat.Coprime u v → H (u * v) = H u * H v)
    (hHr : ∀ p : ℕ, p.Prime → p ∣ r → ∀ j, 1 ≤ j → H (p ^ j) = 0)
    (hrep : ∀ n, H n = ∑ e ∈ (N / M').divisors, c e * Bs b e n)
    (hκ : κ ≠ 0)
    (hfr : ∀ n, κ * H n = cg * ∑ e ∈ (N / M').divisors,
      c e * ((((N / M') / e : ℕ) : ℂ) ^ 2 * Bs b ((N / M') / e) n))
    (hPr : ∀ p : ℕ, p.Prime → p ∣ N / M' → p ∣ r)
    (hv2 : ∀ p : ℕ, p.Prime → p ∣ r → N.factorization p = 2) :
    M' = N := by
  set P := N / M' with hP
  have hM'0 : M' ≠ 0 := by rintro rfl; exact hN (zero_dvd_iff.mp hM'N)
  have hMP : M' * P = N := Nat.mul_div_cancel' hM'N
  have hP0 : P ≠ 0 := by rintro h0; rw [h0, mul_zero] at hMP; exact hN hMP.symm
  by_contra hne
  have hP1 : P ≠ 1 := by intro h1; rw [h1, mul_one] at hMP; exact hne hMP
  -- `c̄ = H ⋆ ν` is multiplicative
  set cb := cbar P c with hcb
  have hHc : toAr H = cb * toAr b := toAr_eq_cbar_mul hP0 hrep
  have hcHν : cb = toAr H * nuAr M' b := by
    rw [hHc, mul_assoc, mul_comm (toAr b), nuAr_mul_toAr hb1 hbmul hbpow, mul_one]
  have hcm : cb.IsMultiplicative := by
    rw [hcHν]; exact (toAr_mult hH1 hHmul).mul (nuAr_mult M' b)
  -- the Fricke relation `κ c_f = c_g c_{P/f} f²` on the divisors of `P`
  have hrel : ∀ f ∈ P.divisors, κ * c f = cg * (c (P / f) * ((f : ℂ) ^ 2)) := by
    have hx : ∀ n, ∑ f ∈ P.divisors, (κ * c f - cg * (c (P / f) * ((f : ℂ) ^ 2))) *
        Bs b f n = 0 := by
      intro n
      have e1 := hfr n
      rw [hrep n, Finset.mul_sum] at e1
      simp only [Bs] at e1 ⊢
      rw [rsum_reindex P n hP0 c b, Finset.mul_sum] at e1
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib] at e1
      refine (Finset.sum_congr rfl fun f _ => ?_).trans e1
      split_ifs <;> ring
    intro f hf
    have := eq_zero_of_sum_Bs hb1 hP0 hx f hf
    linear_combination this
  -- a prime of `P`
  obtain ⟨p, hp, hpP⟩ := Nat.exists_prime_and_dvd hP1
  have hpr := hPr p hp hpP
  have hNp := hv2 p hp hpr
  set v := P.factorization p with hv
  have hv1 : 1 ≤ v := (hp.dvd_iff_one_le_factorization hP0).mp hpP
  have hvM : M'.factorization p + v = 2 := by
    rw [hv, ← hNp, ← hMP, Nat.factorization_mul hM'0 hP0]; rfl
  obtain ⟨Q, hPQ⟩ : p ^ v ∣ P := Nat.ordProj_dvd P p
  have hpQ : Nat.Coprime (p ^ v) Q := by
    refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_)
    have := Nat.pow_succ_factorization_not_dvd hP0 hp
    rw [← hv] at this
    exact this (by rw [hPQ, pow_succ]; exact Nat.mul_dvd_mul_left _ h)
  have hQ0 : Q ≠ 0 := by rintro rfl; rw [mul_zero] at hPQ; exact hP0 hPQ
  have hPv : P / p ^ v = Q := by
    rw [hPQ, Nat.mul_div_cancel_left _ (pow_pos hp.pos v)]
  have hdivP : P ∈ P.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hP0⟩
  have hdivpv : p ^ v ∈ P.divisors := Nat.mem_divisors.mpr ⟨Dvd.intro Q hPQ.symm, hP0⟩
  have hdivQ : Q ∈ P.divisors := Nat.mem_divisors.mpr ⟨Dvd.intro_left _ hPQ.symm, hP0⟩
  have hdiv1 : 1 ∈ P.divisors := Nat.mem_divisors.mpr ⟨one_dvd P, hP0⟩
  -- `c(1) = 1`, `c(P) = c(p^v) c(Q)`
  have hc1 : c 1 = 1 := by rw [← cbar_apply_of_dvd (c := c) hdiv1]; exact hcm.map_one
  have hcP : c P = c (p ^ v) * c Q := by
    rw [← cbar_apply_of_dvd (c := c) hdivP, ← cbar_apply_of_dvd (c := c) hdivpv,
      ← cbar_apply_of_dvd (c := c) hdivQ]
    have := hcm.map_mul_of_coprime hpQ
    rw [← hPQ] at this
    exact this
  -- `c(p^j) = ν(p^j)`
  have hcpj : ∀ j, p ^ j ∈ P.divisors → c (p ^ j) = locN M' b p j := by
    intro j hj
    rw [← cbar_apply_of_dvd (c := c) hj]
    show cb (p ^ j) = _
    rw [hcHν, ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun x y => toAr H x * nuAr M' b y),
      Nat.sum_divisors_prime_pow hp, Finset.sum_eq_single 0]
    · rw [pow_zero, toAr_apply one_ne_zero, hH1, one_mul, Nat.div_one, nuAr_prime_pow hp]
    · intro k hk hk0
      rw [toAr_apply (pow_ne_zero _ hp.ne_zero), hHr p hp hpr k (Nat.pos_of_ne_zero hk0),
        zero_mul]
    · intro h; simp at h
  -- the relation at `f = 1` and `f = p^v`
  have r1 := hrel 1 hdiv1
  rw [hc1, Nat.div_one, hcP] at r1
  have r2 := hrel (p ^ v) hdivpv
  rw [hPv] at r2
  push_cast at r1 r2
  have hcgQ : cg * c Q ≠ 0 := fun h0 => hκ (by linear_combination r1 + c (p ^ v) * h0)
  have hsq : c (p ^ v) ^ 2 = ((p : ℂ) ^ v) ^ 2 := by
    have : cg * c Q * (c (p ^ v) ^ 2 - ((p : ℂ) ^ v) ^ 2) = 0 := by
      linear_combination r2 - c (p ^ v) * r1
    have := (mul_eq_zero.mp this).resolve_left hcgQ
    linear_combination this
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hp1 : (p : ℂ) ^ 2 ≠ 1 := by
    intro h
    have : (p : ℕ) ^ 2 = 1 := by exact_mod_cast h
    have := hp.one_lt
    nlinarith
  by_cases hv2' : v = 2
  · -- `p ∤ M'`: `c(p²) = p`
    have hpM : ¬ p ∣ M' := fun h =>
      absurd ((hp.dvd_iff_one_le_factorization hM'0).mp h) (by omega)
    have hc2 := hcpj 2 (by rw [← hv2']; exact hdivpv)
    rw [hv2', hc2] at hsq
    simp only [locN, hpM] at hsq
    norm_num at hsq
    have : (p : ℂ) ^ 2 * ((p : ℂ) ^ 2 - 1) = 0 := by linear_combination -hsq
    rcases mul_eq_zero.mp this with h | h
    · exact pow_ne_zero 2 hp0 h
    · exact hp1 (by linear_combination h)
  · -- `p ∥ M'`: `c(p)² = b_p² = 1`
    have hv1' : v = 1 := by omega
    have hpM : p ∣ M' := (hp.dvd_iff_one_le_factorization hM'0).mpr (by omega)
    have hpsq : ¬ p ^ 2 ∣ M' := fun h =>
      absurd ((hp.pow_dvd_iff_le_factorization hM'0).mp h) (by omega)
    have hc1' := hcpj 1 (by rw [← hv1']; exact hdivpv)
    rw [hv1', hc1'] at hsq
    simp only [locN] at hsq
    norm_num at hsq
    rw [hbex p hp hpM hpsq] at hsq
    exact hp1 hsq.symm

end ZInQ.GZTheta
