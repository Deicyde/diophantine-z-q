import Mathlib

/-!
# Theorem 5.3, Lane RC11-even: the even form's phase, recurrence and minimum (E.10)–(E.12)

The 11/5 manuscript (`diophantine_zq.tex`), Appendix E, Proposition `ex:app-even-phase`
(tex 7792–8200). The weight-`3/2` form and Waldspurger's coefficient identity are inputs (see
`Prints.lean`, `EvenSource.lean`); this file proves the algebra Elliot builds on them:

* `proportional_of_sq_eq_poly`, `proportional_of_sq_eq` — "(E.10) gives proportional coefficient
  functionals on the whole space": `ℓ_D² = Cℓ₀²` with `C = c²` forces `ℓ_D = ±cℓ₀`, because the
  polynomial ring on the finite-dimensional space is an integral domain (tex 8030–8039);
* `galois_fixed_div`, `pow_half_eq`, `mem_bot_of_fixed` — the Galois comparison: `a(D)/z_D` is
  fixed by every automorphism, hence rational (tex 8104–8134);
* `E11_of_E10`, `Lstar_quotient` — **(E.11)** (tex 8136–8142): `a(D) = z_D r_D`,
  `r_D² = L_*(σD)/L_*(σD₀)`; the period cancels;
* `valuation_eq_zero_of_pow_eq_one` — a two-power root of unity has valuation zero, so nonzero
  coefficients have integral normalized `v₂` (tex 8143–8145);
* `Apr`, `E12_prime_power`, `E12_closed_form` — the closed form of the `T(p²)` recurrence (E.12):
  `a(Dm²) = η(m) a(D) ∏_{p^r ∥ m} A_{p,r}(D)` with integers `A_{p,r}(D)` (tex 8156–8182);
* `even_phase_minimum` — **the finite minimum** (tex 8193–8199): (E.9) and (E.11) make
  `v₂ a(D) − ω(D)` bounded below on the nonzero retained squarefree coefficients; the set is
  nonempty (`D₀`), so it has an attained minimum.

Everything here is PROVED.
-/

namespace ZInQ.Manuscript.RC.Even

open MvPolynomial

/-! ## Proportional functionals (tex 8030–8039) -/

/-- **The domain argument** (tex 8033–8037; PROVED): in the polynomial ring on a
finite-dimensional space (here `K[X_0, …, X_{n−1}]`, an integral domain), `ℓ_D² = c²ℓ₀²` forces
`ℓ_D = cℓ₀` or `ℓ_D = −cℓ₀`. -/
theorem proportional_of_sq_eq_poly {K : Type*} [Field K] {n : ℕ}
    (LD L0 : MvPolynomial (Fin n) K) (c : K) (h : LD ^ 2 = C (c ^ 2) * L0 ^ 2) :
    LD = C c * L0 ∨ LD = -(C c * L0) := by
  have h' : LD ^ 2 = (C c * L0) ^ 2 := by rw [h, mul_pow, map_pow]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp h'

/-- **Proportional coefficient functionals** (tex 8030–8039; PROVED, by Elliot's route through the
polynomial ring): on a finite-dimensional space `V` over an infinite field, if
`ℓ_D(v)² = c² ℓ₀(v)²` for every `v`, then `ℓ_D = cℓ₀` or `ℓ_D = −cℓ₀`. The scalar is common to
every vector; `V` need not be one-dimensional. -/
theorem proportional_of_sq_eq {K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (ℓD ℓ0 : V →ₗ[K] K) (c : K) (h : ∀ v, ℓD v ^ 2 = c ^ 2 * ℓ0 v ^ 2) :
    ℓD = c • ℓ0 ∨ ℓD = -(c • ℓ0) := by
  classical
  let bV := Module.finBasis K V
  -- a linear form, written as a linear polynomial in the coordinates of the basis `bV`
  let P : (V →ₗ[K] K) → MvPolynomial (Fin (Module.finrank K V)) K :=
    fun ℓ => ∑ i, C (ℓ (bV i)) * X i
  have hP : ∀ ℓ (x : Fin (Module.finrank K V) → K), eval x (P ℓ) = ℓ (∑ i, x i • bV i) := by
    intro ℓ x
    simp [P, map_sum, mul_comm]
  have hpoly : P ℓD ^ 2 = C (c ^ 2) * P ℓ0 ^ 2 := by
    apply MvPolynomial.funext
    intro x
    simp only [map_pow, map_mul, eval_C, hP]
    exact h _
  have hcoeff : ∀ ℓ (i : Fin (Module.finrank K V)),
      (P ℓ).coeff (Finsupp.single i 1) = ℓ (bV i) := by
    intro ℓ i
    simp [P, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, Finsupp.single_left_inj]
  rcases proportional_of_sq_eq_poly _ _ c hpoly with H | H
  · left
    refine bV.ext fun i => ?_
    have := congrArg (fun q : MvPolynomial (Fin (Module.finrank K V)) K =>
      q.coeff (Finsupp.single i 1)) H
    simp only [hcoeff, MvPolynomial.coeff_C_mul] at this
    simpa using this
  · right
    refine bV.ext fun i => ?_
    have := congrArg (fun q : MvPolynomial (Fin (Module.finrank K V)) K =>
      q.coeff (Finsupp.single i 1)) H
    simp only [hcoeff, MvPolynomial.coeff_neg, MvPolynomial.coeff_C_mul] at this
    simpa using this

/-! ## The Galois comparison (tex 8086–8134) -/

/-- **`a(D)/z_D` is Galois-fixed** (tex 8104–8132; PROVED): if `τ(z) = z^e` and
`τ(a) = ν(D/D₀) a = z^{e−1} a` with `z ≠ 0`, `e ≥ 1`, then `τ(a/z) = a/z`. -/
theorem galois_fixed_div {K : Type*} [Field K] (τ : K →+* K) {a z : K} (hz : z ≠ 0) {e : ℕ}
    (he : 1 ≤ e) (hτz : τ z = z ^ e) (hτa : τ a = z ^ (e - 1) * a) : τ (a / z) = a / z := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 1 := ⟨e - 1, by omega⟩
  rw [map_div₀, hτz, hτa, Nat.add_sub_cancel, pow_succ, mul_div_mul_left a z (pow_ne_zero k hz)]

/-- `ν(D/D₀) = z_D^{e−1}` (tex 8124–8127; PROVED): with `ν = η^{(e−1)/2}`, `e` odd and
`z_D² = η(D/D₀)`. -/
theorem pow_half_eq {K : Type*} [CommMonoid K] {η z : K} (hz : z ^ 2 = η) {e : ℕ} (he : Odd e) :
    η ^ ((e - 1) / 2) = z ^ (e - 1) := by
  obtain ⟨k, rfl⟩ := he
  have h1 : (2 * k + 1 - 1) / 2 = k := by omega
  have h2 : 2 * k + 1 - 1 = 2 * k := by omega
  rw [h1, h2, ← hz, ← pow_mul]

/-- **Fixed by every automorphism, hence rational** (tex 8131–8132; PROVED, for a finite Galois
extension `K/ℚ` containing all coefficients of the form, tex 8081–8082). -/
theorem mem_bot_of_fixed {K : Type*} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    [IsGalois ℚ K] (x : K) (h : ∀ τ : K ≃ₐ[ℚ] K, τ x = x) : ∃ q : ℚ, (q : K) = x := by
  obtain ⟨q, hq⟩ := (IsGalois.mem_range_algebraMap_iff_fixed x).mpr h
  exact ⟨q, by rw [← hq, eq_ratCast]⟩

/-! ## (E.11) -/

/-- **(E.11) from (E.10)** (tex 8136–8142; PROVED): if (E.10)
`a(D)² = ψ(D/D₀) Q` with `Q = L_*(σD)/L_*(σD₀)`, and `ψ(D/D₀) = z_D²` (because `ψ/η = χ_{−σ}` is
trivial on the local square `D/D₀`), then `r_D = a(D)/z_D` satisfies `a(D) = z_D r_D` and
`r_D² = Q`. -/
theorem E11_of_E10 {K : Type*} [Field K] {aD ψ Q zD : K} (hE10 : aD ^ 2 = ψ * Q)
    (hψ : ψ = zD ^ 2) (hz : zD ≠ 0) : aD = zD * (aD / zD) ∧ (aD / zD) ^ 2 = Q := by
  refine ⟨(mul_div_cancel₀ aD hz).symm, ?_⟩
  rw [div_pow, hE10, hψ]
  field_simp

/-- **The period cancels** (tex 8025–8026; PROVED): for positive `D, D₀` the two central values
`L_*(σD) = √D L(E^{σD},1)/|Ω^σ|` and `L_*(σD₀)` use the same period, so their quotient is
`√D L(E^{σD},1)/(√D₀ L(E^{σD₀},1))`. -/
theorem Lstar_quotient {D D0 L L0 Ω : ℝ} (hΩ : Ω ≠ 0) :
    (Real.sqrt D * L / Ω) / (Real.sqrt D0 * L0 / Ω) = (Real.sqrt D * L) / (Real.sqrt D0 * L0) := by
  rw [div_div_div_cancel_right₀ hΩ]

/-- **A root of unity has valuation zero** (tex 8143–8145, 8185–8187; PROVED): for any additive
valuation with values in a linearly ordered group, `z^n = 1` with `n > 0` gives `v(z) = 0`; hence
`v(z_D r_D) = v(r_D)` and nonzero coefficients have integral normalized `v₂`. -/
theorem valuation_eq_zero_of_pow_eq_one {K Γ : Type*} [Field K] [AddCommGroup Γ] [LinearOrder Γ]
    [IsOrderedAddMonoid Γ] (v : AddValuation K (WithTop Γ)) {z : K} {n : ℕ} (hn : 0 < n)
    (hz : z ^ n = 1) : v z = 0 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn.ne'] at hz
    exact zero_ne_one hz
  have h1 : n • v z = 0 := by rw [← AddValuation.map_pow, hz, AddValuation.map_one]
  obtain ⟨γ, hγ⟩ := WithTop.ne_top_iff_exists.mp ((AddValuation.ne_top_iff v).mpr hz0)
  rw [← hγ] at h1 ⊢
  rw [← WithTop.coe_nsmul, ← WithTop.coe_zero, WithTop.coe_eq_coe] at h1
  have hγ0 : γ = 0 := by
    rcases lt_trichotomy γ 0 with h | h | h
    · exact absurd h1 (nsmul_neg h hn.ne').ne
    · exact h
    · exact absurd h1 (nsmul_pos h hn.ne').ne'
  rw [hγ0, WithTop.coe_zero]

/-! ## The closed form of the `T(p²)` recurrence (E.12) -/

/-- **`A_{p,r}(D)`** (tex 8168–8171), with `c = (ψ/η)(p)·(−D/p)`:
`A_{p,0} = 1`, `A_{p,1} = a_p − c`, `A_{p,r+2} = a_p A_{p,r+1} − p A_{p,r}`. All are integers. -/
def Apr (ap : ℤ) (p : ℕ) (c : ℤ) : ℕ → ℤ
  | 0 => 1
  | 1 => ap - c
  | (r + 2) => ap * Apr ap p c (r + 1) - p * Apr ap p c r

/-- **(E.12) at one good prime** (tex 8156–8166; PROVED). Let `a : ℕ → K` satisfy the good
`T(p²)` recurrence at the prime `p`:
`a(p²n) = {η(p)a_p − ψ(p)(−n/p)} a(n) − p η(p)² a(n/p²)` for every `n ≥ 1` (the last term read as
`0` when `p² ∤ n`), with `ψ(p) = η(p)χ` for the integer `χ = (ψ/η)(p)`. For `D` squarefree and `m'`
prime to `p`, `a(D m'² p^{2r}) = η(p)^r A_{p,r}(D) a(D m'²)`. -/
theorem E12_prime_power {K : Type*} [Field K] (a : ℕ → K) {p : ℕ} (hp : p.Prime)
    (ηp ψp : K) (ap χ : ℤ) (hψ : ψp = ηp * χ)
    (hrec : ∀ n : ℕ, 0 < n → a (p ^ 2 * n) =
      (ηp * ap - ψp * (jacobiSym (-(n : ℤ)) p : K)) * a n -
        p * ηp ^ 2 * (if p ^ 2 ∣ n then a (n / p ^ 2) else 0))
    {D m' : ℕ} (hD : Squarefree D) (hm' : ¬ p ∣ m') (hD0 : 0 < D) (hm'0 : 0 < m') (r : ℕ) :
    a (D * m' ^ 2 * p ^ (2 * r)) =
      ηp ^ r * (Apr ap p (χ * jacobiSym (-(D : ℤ)) p) r : K) * a (D * m' ^ 2) := by
  set c := χ * jacobiSym (-(D : ℤ)) p with hc
  set N := D * m' ^ 2 with hN
  have hN0 : 0 < N := by positivity
  have hp0 : 0 < p := hp.pos
  -- the first step: `p² ∤ D m'²` and `(−Dm'²/p) = (−D/p)`
  have hndvd : ¬ p ^ 2 ∣ N := by
    intro hdvd
    have hcop : Nat.Coprime (p ^ 2) (m' ^ 2) :=
      Nat.Coprime.pow 2 2 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm')
    have hpD : p ^ 2 ∣ D := hcop.dvd_of_dvd_mul_right hdvd
    have hpp : p * p ∣ D := by rwa [← pow_two]
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hD p hpp))
  have hJN : jacobiSym (-(N : ℤ)) p = jacobiSym (-(D : ℤ)) p := by
    have hgcd : Int.gcd (m' : ℤ) (p : ℤ) = 1 := by
      rw [Int.gcd_natCast_natCast]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm')
    rw [hN, Nat.cast_mul, Nat.cast_pow, neg_mul_eq_neg_mul, jacobiSym.mul_left,
      jacobiSym.sq_one' hgcd, mul_one]
  have h1 : a (N * p ^ (2 * 1)) = ηp ^ 1 * (Apr ap p c 1 : K) * a N := by
    rw [show N * p ^ (2 * 1) = p ^ 2 * N by ring, hrec N hN0, ite_eq_right hndvd, hJN, hψ]
    simp only [Apr, hc]
    push_cast
    ring
  -- the two-step recurrence
  have key : ∀ r, a (N * p ^ (2 * r)) = ηp ^ r * (Apr ap p c r : K) * a N ∧
      a (N * p ^ (2 * (r + 1))) = ηp ^ (r + 1) * (Apr ap p c (r + 1) : K) * a N := by
    intro r
    induction r with
    | zero => exact ⟨by simp [Apr], by simpa using h1⟩
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have hpos : 0 < N * p ^ (2 * (k + 1)) := by positivity
      have hdvd : p ^ 2 ∣ N * p ^ (2 * (k + 1)) :=
        ⟨N * p ^ (2 * k), by ring⟩
      have hdiv : N * p ^ (2 * (k + 1)) / p ^ 2 = N * p ^ (2 * k) := by
        rw [show N * p ^ (2 * (k + 1)) = p ^ 2 * (N * p ^ (2 * k)) by ring]
        exact Nat.mul_div_cancel_left _ (by positivity)
      have hgcdp : Int.gcd (p : ℤ) (p : ℤ) ≠ 1 := by
        rw [Int.gcd_natCast_natCast, Nat.gcd_self]
        exact hp.ne_one
      have hJp : jacobiSym (p : ℤ) p = 0 := jacobiSym.eq_zero_iff.mpr ⟨hp.ne_zero, hgcdp⟩
      have hJ0 : jacobiSym (-((N * p ^ (2 * (k + 1)) : ℕ) : ℤ)) p = 0 := by
        rw [Nat.cast_mul, Nat.cast_pow, neg_mul_eq_neg_mul, jacobiSym.mul_left,
          jacobiSym.pow_left, hJp, zero_pow (by omega), mul_zero]
      rw [show N * p ^ (2 * (k + 1 + 1)) = p ^ 2 * (N * p ^ (2 * (k + 1))) by ring,
        hrec _ hpos, ite_eq_left hdvd, hdiv, hJ0, ih.1, ih.2]
      simp only [Apr]
      push_cast
      ring
  exact (key r).1

/-- **(E.12), the closed form** (tex 8172–8182; PROVED): if the recurrence of `E12_prime_power`
holds at every prime outside `S₁`, then for squarefree `D > 0` and `m > 0` with all prime factors
outside `S₁`,
`a(Dm²) = (∏_{p^r ∥ m} η(p)^r A_{p,r}(D)) a(D)`; with `a(D) = z_D r_D` this is Elliot's
`a(Dm²) = z_D η(m) r_D ∏_{p^r ∥ m} A_{p,r}(D)`. -/
theorem E12_closed_form {K : Type*} [Field K] (a : ℕ → K) (S₁ : Finset ℕ) (η ψ : ℕ → K)
    (ap χ : ℕ → ℤ) (hψ : ∀ p, p.Prime → p ∉ S₁ → ψ p = η p * χ p)
    (hrec : ∀ p, p.Prime → p ∉ S₁ → ∀ n : ℕ, 0 < n → a (p ^ 2 * n) =
      (η p * ap p - ψ p * (jacobiSym (-(n : ℤ)) p : K)) * a n -
        p * (η p) ^ 2 * (if p ^ 2 ∣ n then a (n / p ^ 2) else 0))
    {D : ℕ} (hD : Squarefree D) (hD0 : 0 < D) {m : ℕ} (hm : 0 < m)
    (hmS : ∀ p ∈ m.primeFactors, p ∉ S₁) :
    a (D * m ^ 2) = (∏ p ∈ m.primeFactors, (η p) ^ (m.factorization p) *
      (Apr (ap p) p (χ p * jacobiSym (-(D : ℤ)) p) (m.factorization p) : K)) * a D := by
  induction m using Nat.recOnPrimePow with
  | zero => exact absurd hm (lt_irrefl 0)
  | one => simp
  | prime_pow_mul b p n hp hpb hn ih =>
    have hpn0 : p ^ n ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hb0 : 0 < b := Nat.pos_of_ne_zero fun hb => by simp [hb] at hm
    have hpf : (p ^ n * b).primeFactors = insert p b.primeFactors := by
      rw [Nat.primeFactors_mul hpn0 hb0.ne', Nat.primeFactors_prime_pow hn.ne' hp,
        Finset.insert_eq]
    have hpS : p ∉ S₁ := hmS p (by rw [hpf]; exact Finset.mem_insert_self _ _)
    have hbS : ∀ q ∈ b.primeFactors, q ∉ S₁ := fun q hq =>
      hmS q (by rw [hpf]; exact Finset.mem_insert_of_mem hq)
    have hpnot : p ∉ b.primeFactors := fun h => hpb (Nat.dvd_of_mem_primeFactors h)
    have hfac : (p ^ n * b).factorization = Finsupp.single p n + b.factorization := by
      rw [Nat.factorization_mul hpn0 hb0.ne', hp.factorization_pow]
    have hfp : (p ^ n * b).factorization p = n := by
      rw [hfac, Finsupp.add_apply, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd hpb, add_zero]
    have hfq : ∀ q ∈ b.primeFactors, (p ^ n * b).factorization q = b.factorization q := by
      intro q hq
      have hqp : q ≠ p := fun h => hpnot (h ▸ hq)
      rw [hfac, Finsupp.add_apply, Finsupp.single_eq_of_ne hqp, zero_add]
    have hE := E12_prime_power a hp (η p) (ψ p) (ap p) (χ p) (hψ p hp hpS) (hrec p hp hpS) hD
      hpb hD0 hb0 n
    have hprod : ∏ q ∈ b.primeFactors, η q ^ (p ^ n * b).factorization q *
        (Apr (ap q) q (χ q * jacobiSym (-(D : ℤ)) q) ((p ^ n * b).factorization q) : K) =
        ∏ q ∈ b.primeFactors, η q ^ b.factorization q *
        (Apr (ap q) q (χ q * jacobiSym (-(D : ℤ)) q) (b.factorization q) : K) :=
      Finset.prod_congr rfl fun q hq => by rw [hfq q hq]
    rw [show D * (p ^ n * b) ^ 2 = D * b ^ 2 * p ^ (2 * n) by ring, hE, ih hb0 hbS, hpf,
      Finset.prod_insert hpnot, hfp, hprod]
    ring

/-! ## The finite minimum (tex 8193–8199) -/

/-- `ω(n)` for a natural number: the number of distinct prime factors. -/
def omegaN (n : ℕ) : ℕ := n.primeFactors.card

/-- **The finite attained minimum of `v₂ a(D) − ω(D)`** (tex 7807–7810, 8193–8199; PROVED).
Let `𝒟` be the retained positive squarefree parameters, `D₀ ∈ 𝒟` the reference with
`L_*(σD₀) ≠ 0`, and `r_D ∈ ℚ` the rational parts of (E.11): `r_D² = L_*(σD)/L_*(σD₀)` (so
`v₂ a(D) = v₂ r_D`). If (E.9) holds — `v₂ L_*(h) ≥ 2ω(h) + s(h) − c_E − C_loc` whenever
`L_*(h) ≠ 0` — then the values `v₂ r_D − ω(D)` at nonzero coefficients have an attained minimum
`δ`. (`σ = ±1`, so `ω(σD) = ω(D)`.) -/
theorem even_phase_minimum (Lstar : ℤ → ℚ) (s : ℤ → ℕ) (σ : ℤ) (hσ : σ = 1 ∨ σ = -1)
    (𝒟 : Set ℕ) {D0 : ℕ} (hD0 : D0 ∈ 𝒟) (hL0 : Lstar (σ * D0) ≠ 0) (r : ℕ → ℚ)
    (hr : ∀ D ∈ 𝒟, r D ^ 2 = Lstar (σ * D) / Lstar (σ * D0)) (cE Cloc : ℤ)
    (hE9 : ∀ h : ℤ, Lstar h ≠ 0 →
      2 * (h.natAbs.primeFactors.card : ℤ) + s h - cE - Cloc ≤ padicValRat 2 (Lstar h)) :
    ∃ δ : ℤ, (∃ D ∈ 𝒟, r D ≠ 0 ∧ padicValRat 2 (r D) - omegaN D = δ) ∧
      ∀ D ∈ 𝒟, r D ≠ 0 → δ ≤ padicValRat 2 (r D) - omegaN D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = cE + Cloc + padicValRat 2 (Lstar (σ * D0)) := ⟨_, rfl⟩
  -- (E.9) and (E.11) bound `v₂ r_D − ω(D)` below by `−|B|`
  have hbound : ∀ D ∈ 𝒟, r D ≠ 0 → -|B| ≤ padicValRat 2 (r D) - omegaN D := by
    intro D hD hrD
    have hLD : Lstar (σ * D) ≠ 0 := by
      intro h0
      have h2 := hr D hD
      rw [h0, zero_div] at h2
      exact hrD (pow_eq_zero_iff two_ne_zero |>.mp h2)
    have hv : 2 * padicValRat 2 (r D) =
        padicValRat 2 (Lstar (σ * D)) - padicValRat 2 (Lstar (σ * D0)) := by
      have h2 := congrArg (padicValRat 2) (hr D hD)
      rw [padicValRat.pow, padicValRat.div hLD hL0] at h2
      exact_mod_cast h2
    have hω : (σ * (D : ℤ)).natAbs = D := by
      rcases hσ with rfl | rfl <;> simp
    have h9 := hE9 _ hLD
    rw [hω] at h9
    have hs : (0 : ℤ) ≤ (s (σ * D) : ℤ) := Int.natCast_nonneg _
    have habs := le_abs_self B
    have habs0 := abs_nonneg B
    unfold omegaN
    linarith
  have hr0 : r D0 ≠ 0 := by
    intro h0
    have h2 := hr D0 hD0
    rw [h0, div_self hL0] at h2
    norm_num at h2
  obtain ⟨δ, ⟨D, hD, hrD, rfl⟩, hmin⟩ := Int.exists_least_of_bdd
    (P := fun z => ∃ D ∈ 𝒟, r D ≠ 0 ∧ padicValRat 2 (r D) - omegaN D = z)
    ⟨-|B|, by rintro z ⟨D, hD, hrD, rfl⟩; exact hbound D hD hrD⟩
    ⟨_, D0, hD0, hr0, rfl⟩
  exact ⟨_, ⟨D, hD, hrD, rfl⟩, fun D' hD' hrD' => hmin _ ⟨D', hD', hrD', rfl⟩⟩

end ZInQ.Manuscript.RC.Even
