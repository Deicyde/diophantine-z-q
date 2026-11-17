import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Waldspurger
import ZInQKernel.Contrib.OneProof.RC.Even.EvenSource

/-!
# Theorem 5.3, Lane RC11-even: the actual even form, (E.10)–(E.12) and its minimum

The 11/5 manuscript (`diophantine_zq.tex`), Appendix E, Proposition `ex:app-even-phase`
(tex 7792–8200). The weight-`3/2` forms, their Fourier coefficients and Shimura's `T(p²)` are
lane RC8's genuine definitions (`IsHalfIntegralWeightCuspForm`, `hiwCoeff`, `heckeT3`,
`IsInWaldspurgerEigenspace`), and Waldspurger's Corollaire 2 is lane RC8's PRINT leaf
`WaldspurgerCor2`. This file proves:

* `E10_of_waldspurgerCor2` — **(E.10)** (tex 7968–8028): for `g` in the good-Hecke eigenspace and
  `D, D₀` in one unit squareclass at the level, `(a(D)/a(D₀))² = ψ(D)ψ(D₀)⁻¹ L_*(σD)/L_*(σD₀)`:
  "dividing only by the nonzero reference value", and the period cancels;
* `E12_of_eigenspace` — **(E.12)** (tex 8156–8161): the good `T(p²)` recurrence
  `a(p²n) = {η(p)a_p − ψ(p)(−n/p)} a(n) − pη(p)² a(n/p²)`, from the eigenvalue equation and
  `ψ² = η²`; `closedForm_of_eigenspace` — its closed form with integer `A_{p,r}(D)`
  (tex 8162–8182);
* `EvenPhaseData` — the remaining inputs of the proposition (ELLIOT: the nonzero reference form
  with scalar character and level on `S₀`, the phase `z_D` and the Galois comparison
  `a(D)/z_D ∈ ℚ`, tex 7812–7940, 8041–8134);
* `EvenPhaseData.E11` — **(E.11)** (tex 8136–8142): `a(D) = z_D r_D`, `r_D ∈ ℚ`,
  `r_D² = L_*(σD)/L_*(σD₀)`;
* `EvenPhaseData.minimum` — **the attained minimum** of `v₂ a(D) − ω(D)` (tex 7807–7810,
  8193–8199), from (E.9) and (E.11).
-/

noncomputable section

namespace ZInQ.Manuscript.RC.Even

open ZInQ.Manuscript ZInQ.Contrib.CloudB3RC53 ZInQ.Manuscript.RC.PrintsAnalytic

/-! ## (E.10) from Waldspurger's Corollaire 2 -/

/-- `σD` and `σD₀` have the same sign, so the same period (PROVED). -/
theorem period_same_sign {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {D D₀ : ℕ} (hD : 0 < D) (hD₀ : 0 < D₀) :
    (0 < σ * (D : ℤ) ↔ 0 < σ * (D₀ : ℤ)) := by
  rcases hσ with rfl | rfl <;> constructor <;> intro h <;> omega

/-- `|σD| = D` for `σ = ±1` (PROVED). -/
theorem abs_sigma_mul {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) (D : ℕ) :
    |((σ * (D : ℤ) : ℤ) : ℝ)| = (D : ℝ) := by
  rcases hσ with rfl | rfl <;> simp

/-- `σD ≠ 0` for `σ = ±1` and `D > 0` (PROVED), so the anchor of `L_*` applies at `σD`. -/
theorem sigma_mul_ne_zero {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {D : ℕ} (hD : 0 < D) :
    σ * (D : ℤ) ≠ 0 := by
  rcases hσ with rfl | rfl <;> omega

/-- **(E.10)** (tex 7968–8028; PROVED from lane RC8's PRINT `WaldspurgerCor2` and the anchor of
`L_*`). Let `g` lie in the good-Hecke eigenspace of `E` and `η = ψχ_{−σ}` at a level `N`
(`4 ∣ N`), and let `D₀, D` be positive squarefree, prime to `N`, in one unit squareclass at every
prime of `N`, with `a(D₀) ≠ 0` and `L_*(σD₀) ≠ 0`. Then
`(a(D)/a(D₀))² = ψ(D) ψ(D₀)⁻¹ · L_*(σD)/L_*(σD₀)`. -/
theorem E10_of_waldspurgerCor2 (hW : WaldspurgerCor2) {E : WeierstrassCurve ℚ} (hE : E.IsElliptic)
    (L : CentralNormalization E) {N : ℕ} (hN : 4 ∣ N) (ψ η : DirichletCharacter ℂ N) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ))
    {g : UpperHalfPlane → ℂ} (hg : IsInWaldspurgerEigenspace E N ψ η g) {D₀ D : ℕ}
    (hD₀ : 0 < D₀) (hD : 0 < D) (hsq₀ : Squarefree D₀) (hsq : Squarefree D)
    (hc₀ : D₀.Coprime N) (hc : D.Coprime N) (hcl : SameUnitClassesAtLevel N D D₀)
    {F₀ F : ℂ → ℂ} (hF₀ : IsLContinuation (qtwist E ((σ * D₀ : ℤ) : ℚ)) F₀)
    (hF : IsLContinuation (qtwist E ((σ * D : ℤ) : ℚ)) F) (ha₀ : hiwCoeff g D₀ ≠ 0)
    (hL₀ : L.Lstar (σ * D₀) ≠ 0) :
    (hiwCoeff g D / hiwCoeff g D₀) ^ 2 =
      ψ D * (ψ D₀)⁻¹ * (((L.Lstar (σ * D) / L.Lstar (σ * D₀) : ℚ) : ℝ) : ℂ) := by
  -- Corollaire 2 in its printed order
  have hW' := hW E hE N hN ψ η σ hσ hψη g hg D₀ D hD₀ hD hsq₀ hsq hc₀ hc hcl F₀ F hF₀ hF
  -- the anchors `L_*(σD) = √D F(1)/Ω`, `L_*(σD₀) = √D₀ F₀(1)/Ω` with one period `Ω`
  have hA := L.anchor _ (sigma_mul_ne_zero hσ hD) F hF
  have hA₀ := L.anchor _ (sigma_mul_ne_zero hσ hD₀) F₀ hF₀
  rw [abs_sigma_mul hσ] at hA hA₀
  simp only [period_same_sign hσ hD hD₀] at hA
  set Ω : ℝ := if 0 < σ * (D₀ : ℤ) then L.Ωp else L.Ωm with hΩdef
  have hΩ : (Ω : ℂ) ≠ 0 := by
    have : Ω ≠ 0 := by
      rw [hΩdef]
      split_ifs
      · exact L.Ωp_pos.ne'
      · exact L.Ωm_pos.ne'
    exact_mod_cast this
  have hs₀ : (Real.sqrt (D₀ : ℝ) : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt (D₀ : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hD₀)
    exact_mod_cast this.ne'
  -- the reference value is nonzero
  have hF₀1 : F₀ 1 ≠ 0 := by
    intro h0
    apply hL₀
    have : (((L.Lstar (σ * D₀) : ℚ) : ℝ) : ℂ) = 0 := by rw [hA₀, h0, mul_zero, zero_div]
    exact_mod_cast this
  have hcast : (((L.Lstar (σ * D) / L.Lstar (σ * D₀) : ℚ) : ℝ) : ℂ) =
      (((L.Lstar (σ * D) : ℚ) : ℝ) : ℂ) / (((L.Lstar (σ * D₀) : ℚ) : ℝ) : ℂ) := by
    rw [Rat.cast_div, Complex.ofReal_div]
  -- divide only by the nonzero reference value; the period cancels
  rw [hcast, hA, hA₀, div_pow]
  field_simp
  linear_combination -hW'

/-! ## (E.12) from the eigenvalue equation -/

/-- `χ_{−σ}(p)² = 1` at a prime `p ∤ N` when `4 ∣ N` (PROVED): such `p` is odd, so
`χ_{−σ}(p)` is the Jacobi symbol `(∓1/p) = ±1`. -/
theorem kronecker_neg_sigma_sq {N : ℕ} (hN : 4 ∣ N) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {p : ℕ}
    (hp : p.Prime) (hpN : ¬ p ∣ N) : kronecker (-σ) p ^ 2 = 1 := by
  have h2p : ¬ 2 ∣ p := by
    intro h
    have hp2 : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp h).symm
    exact hpN (hp2 ▸ dvd_trans (by norm_num) hN)
  have hfac : p.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2p
  unfold kronecker
  rw [hfac, pow_zero, pow_zero, one_mul, Nat.div_one]
  apply jacobiSym.sq_one
  rcases hσ with rfl | rfl <;> simp

/-- `η(p)² = ψ(p)²` at a prime `p ∤ N` (PROVED): `ψ/η = χ_{−σ}` is quadratic. -/
theorem eta_sq_eq_psi_sq {N : ℕ} (hN : 4 ∣ N) (ψ η : DirichletCharacter ℂ N) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ))
    {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) : η p ^ 2 = ψ p ^ 2 := by
  have hk : ((kronecker (-σ) p : ℤ) : ℂ) ^ 2 = 1 := by
    exact_mod_cast kronecker_neg_sigma_sq hN hσ hp hpN
  rw [hψη p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN), mul_pow, hk, mul_one]

/-- **(E.12)** (tex 8156–8161; PROVED from lane RC8's eigenspace condition): at a prime `p ∤ N`,
`a(p²n) = {η(p)a_p − ψ(p)(−n/p)} a(n) − pη(p)² a(n/p²)`, using `ψ(p)² = η(p)²`
(`ψ/η = χ_{−σ}` is quadratic). -/
theorem E12_of_eigenspace {E : WeierstrassCurve ℚ} {N : ℕ} (hN : 4 ∣ N)
    (ψ η : DirichletCharacter ℂ N) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ))
    {g : UpperHalfPlane → ℂ} (hg : IsInWaldspurgerEigenspace E N ψ η g) {p : ℕ} (hp : p.Prime)
    (hpN : ¬ p ∣ N) (n : ℕ) :
    hiwCoeff g (p ^ 2 * n) =
      (η p * lcoeff E p - ψ p * (jacobiSym (-(n : ℤ)) p : ℂ)) * hiwCoeff g n -
        p * (η p) ^ 2 * (if p ^ 2 ∣ n then hiwCoeff g (n / p ^ 2) else 0) := by
  have h := hg.2 p hp hpN n
  unfold heckeT3 at h
  rw [eta_sq_eq_psi_sq hN ψ η hσ hψη hp hpN]
  linear_combination h

/-- **The closed form of (E.12)** (tex 8162–8182; PROVED from `E12_of_eigenspace` and
`E12_closed_form`): for squarefree `D > 0` and `m > 0` prime to `N`,
`a(Dm²) = (∏_{p^r ∥ m} η(p)^r A_{p,r}(D)) a(D)` with the integers
`A_{p,r}(D)` of `Apr` (`c = χ_{−σ}(p)(−D/p)`). -/
theorem closedForm_of_eigenspace {E : WeierstrassCurve ℚ} {N : ℕ} (hN : 4 ∣ N)
    (ψ η : DirichletCharacter ℂ N) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1)
    (hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ))
    {g : UpperHalfPlane → ℂ} (hg : IsInWaldspurgerEigenspace E N ψ η g) {D : ℕ}
    (hD : Squarefree D) (hD0 : 0 < D) {m : ℕ} (hm : 0 < m) (hmN : m.Coprime N) :
    hiwCoeff g (D * m ^ 2) = (∏ p ∈ m.primeFactors, (η p) ^ (m.factorization p) *
      (Apr (E.LFunction p) p (kronecker (-σ) p * jacobiSym (-(D : ℤ)) p)
        (m.factorization p) : ℂ)) * hiwCoeff g D := by
  rcases Nat.eq_zero_or_pos N with rfl | hN0
  · -- level `0`: `m` is prime to `0`, so `m = 1` and the product is empty
    have hm1 : m = 1 := (Nat.coprime_zero_right m).mp hmN
    subst hm1
    simp
  · -- the bad primes are the prime factors of `N`
    have hS : ∀ p, p.Prime → p ∉ N.primeFactors → ¬ p ∣ N := fun p hp hpS h =>
      hpS (Nat.mem_primeFactors.mpr ⟨hp, h, hN0.ne'⟩)
    refine E12_closed_form (hiwCoeff g) N.primeFactors (fun p => η p) (fun p => ψ p)
      (fun p => E.LFunction p) (fun p => kronecker (-σ) p) ?_ ?_ hD hD0 hm ?_
    · -- `ψ(p) = η(p) χ_{−σ}(p)`, since `χ_{−σ}(p)² = 1`
      intro p hp hpS
      have hpN := hS p hp hpS
      have hk : ((kronecker (-σ) p : ℤ) : ℂ) ^ 2 = 1 := by
        exact_mod_cast kronecker_neg_sigma_sq hN hσ hp hpN
      show ψ p = η p * (kronecker (-σ) p : ℂ)
      rw [hψη p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN), mul_assoc, ← sq, hk, mul_one]
    · -- the good `T(p²)` recurrence
      intro p hp hpS n _
      exact E12_of_eigenspace hN ψ η hσ hψη hg hp (hS p hp hpS) n
    · -- the primes of `m` are good
      intro p hpm hpS
      exact (Nat.Prime.coprime_iff_not_dvd (Nat.prime_of_mem_primeFactors hpm)).mp
        (Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hpm) hmN)
        (Nat.dvd_of_mem_primeFactors hpS)

/-! ## The proposition `ex:app-even-phase` -/

/-- **The actual even form and its phase** (Proposition `ex:app-even-phase`, tex 7792–7811;
ELLIOT inputs). For the fixed sign `σ = ±1` and positive squarefree reference `D₀` with
`L_*(σD₀) ≠ 0`:
* `N, ψ, η, g` — the nonzero reference form: a weight-`3/2` cusp form in the full good-Hecke
  eigenspace of `E` and `η = ψχ_{−σ}`, at a level `N` (`4 ∣ N`) supported on `S₀`, with
  `a(D₀) ≠ 0` (Waldspurger's theta theorem and Elliot's local scalar type, tex 7821–7940; RC8's
  `WaldspurgerNonvanishing`);
* `retained` — the retained positive squarefree `D` (prime to `N`, in the unit squareclasses of
  `D₀` at every prime of the level), containing `D₀`;
* `z` — the phase `z_D = ∏_{p ∣ cond η} η_p(u_p)` with `u_p² = D/D₀` (tex 8116–8128): a two-power
  root of unity with `z_D² = η(D/D₀) = ψ(D/D₀)` (`ψ/η = χ_{−σ}` is trivial on the local square
  `D/D₀`, tex 8136–8138);
* `rational` — the Galois comparison (tex 8086–8134, on Ramsey's algebraic model,
  tex 8041–8083): `a(D)/(a(D₀) z_D)` is fixed by every automorphism of `ℚ̄`, hence rational
  (PROVED algebra: `galois_fixed_div`, `pow_half_eq`, `mem_bot_of_fixed`). -/
structure EvenPhaseData (E : WeierstrassCurve ℚ) (L : CentralNormalization E) (σ : ℤ) (D₀ : ℕ)
    where
  N : ℕ
  hN : 4 ∣ N
  ψ : DirichletCharacter ℂ N
  η : DirichletCharacter ℂ N
  hψη : ∀ n : ℕ, n.Coprime N → η n = ψ n * (kronecker (-σ) n : ℂ)
  g : UpperHalfPlane → ℂ
  hg : IsInWaldspurgerEigenspace E N ψ η g
  ha₀ : hiwCoeff g D₀ ≠ 0
  retained : Set ℕ
  retained_spec : ∀ D ∈ retained,
    0 < D ∧ Squarefree D ∧ D.Coprime N ∧ SameUnitClassesAtLevel N D D₀
  D₀_mem : D₀ ∈ retained
  z : ℕ → ℂ
  z_root : ∀ D ∈ retained, ∃ k : ℕ, z D ^ (2 ^ k) = 1
  z_sq : ∀ D ∈ retained, z D ^ 2 = ψ D * (ψ D₀)⁻¹
  rational : ∀ D ∈ retained, ∃ r : ℚ, hiwCoeff g D / hiwCoeff g D₀ = z D * (r : ℂ)

/-- **(E.11)** (tex 8136–8142; PROVED from `E10_of_waldspurgerCor2` and `E11_of_E10`): with the
normalization `a(D₀) = 1` (that is, `a(D) := a_g(D)/a_g(D₀)`), every retained `D` has
`a(D) = z_D r_D` with `r_D ∈ ℚ` and `r_D² = L_*(σD)/L_*(σD₀)`. -/
theorem EvenPhaseData.E11 (hW : WaldspurgerCor2) {E : WeierstrassCurve ℚ} (hE : E.IsElliptic)
    {L : CentralNormalization E} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {D₀ : ℕ}
    (P : EvenPhaseData E L σ D₀) (hL₀ : L.Lstar (σ * D₀) ≠ 0)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist E h) F) :
    ∀ D ∈ P.retained, ∃ r : ℚ, hiwCoeff P.g D / hiwCoeff P.g D₀ = P.z D * (r : ℂ) ∧
      r ^ 2 = L.Lstar (σ * D) / L.Lstar (σ * D₀) := by
  intro D hD
  obtain ⟨r, hr⟩ := P.rational D hD
  refine ⟨r, hr, ?_⟩
  obtain ⟨hD0, hsq, hc, hcl⟩ := P.retained_spec D hD
  obtain ⟨hD₀0, hsq₀, hc₀, -⟩ := P.retained_spec D₀ P.D₀_mem
  obtain ⟨F, hF⟩ := hcont _ (sigma_mul_ne_zero hσ hD0)
  obtain ⟨F₀, hF₀⟩ := hcont _ (sigma_mul_ne_zero hσ hD₀0)
  -- (E.10), with `ψ(D)ψ(D₀)⁻¹ = z_D²` and `a(D) = z_D r_D`
  have h10 := E10_of_waldspurgerCor2 hW hE L P.hN P.ψ P.η hσ P.hψη P.hg hD₀0 hD0 hsq₀ hsq hc₀ hc
    hcl hF₀ hF P.ha₀ hL₀
  rw [hr, ← P.z_sq D hD, mul_pow] at h10
  -- `z_D` is a root of unity, so nonzero
  have hz : P.z D ≠ 0 := by
    obtain ⟨k, hk⟩ := P.z_root D hD
    rintro h0
    rw [h0, zero_pow (pow_ne_zero k two_ne_zero)] at hk
    exact zero_ne_one hk
  have h' : (r : ℂ) ^ 2 = (((L.Lstar (σ * D) / L.Lstar (σ * D₀) : ℚ) : ℝ) : ℂ) :=
    mul_left_cancel₀ (pow_ne_zero 2 hz) h10
  exact_mod_cast h'

/-- **The finite attained minimum of `v₂ a(D) − ω(D)`** (tex 7807–7810, 8193–8199; PROVED from
(E.11) and (E.9) via `even_phase_minimum`): among the retained `D` with nonzero coefficient, the
values `v₂ r_D − ω(D)` (`v₂ a(D) = v₂ r_D`, since `z_D` is a root of unity) have a least element.
(E.9) is only needed at the retained `σD`, which are odd (`D` is prime to `N`, `2 ∣ N`) and
squarefree, so `EvenLowerBound` applies to `L_*` restricted to them. -/
theorem EvenPhaseData.minimum (hW : WaldspurgerCor2) {E : WeierstrassCurve ℚ} (hE : E.IsElliptic)
    {L : CentralNormalization E} {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) {D₀ : ℕ}
    (P : EvenPhaseData E L σ D₀) (hL₀ : L.Lstar (σ * D₀) ≠ 0)
    (hcont : ∀ h : ℤ, h ≠ 0 → ∃ F, IsLContinuation (qtwist E h) F)
    (h9 : EvenLowerBound E L) :
    ∃ r : ℕ → ℚ, (∀ D ∈ P.retained, hiwCoeff P.g D / hiwCoeff P.g D₀ = P.z D * (r D : ℂ) ∧
        r D ^ 2 = L.Lstar (σ * D) / L.Lstar (σ * D₀)) ∧
      ∃ δ : ℤ, (∃ D ∈ P.retained, r D ≠ 0 ∧ padicValRat 2 (r D) - omegaN D = δ) ∧
        ∀ D ∈ P.retained, r D ≠ 0 → δ ≤ padicValRat 2 (r D) - omegaN D := by
  classical
  -- the rational parts `r_D` of (E.11), extended by `0` outside the retained set
  have hE11 := P.E11 hW hE hσ hL₀ hcont
  have hex : ∀ D : ℕ, ∃ q : ℚ, D ∈ P.retained →
      (hiwCoeff P.g D / hiwCoeff P.g D₀ = P.z D * (q : ℂ) ∧
        q ^ 2 = L.Lstar (σ * D) / L.Lstar (σ * D₀)) := by
    intro D
    by_cases hD : D ∈ P.retained
    · obtain ⟨q, hq⟩ := hE11 D hD
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => absurd h hD⟩
  choose r hr using hex
  refine ⟨r, hr, ?_⟩
  obtain ⟨C, hC⟩ := h9
  -- `L_*` restricted to the retained values `σD` (zero elsewhere): (E.9) is only needed there
  set Lstar' : ℤ → ℚ := fun h =>
    if ∃ D ∈ P.retained, h = σ * (D : ℤ) then L.Lstar h else 0 with hLdef
  have hL' : ∀ D ∈ P.retained, Lstar' (σ * D) = L.Lstar (σ * D) := fun D hD =>
    ite_eq_left ⟨D, hD, rfl⟩
  refine even_phase_minimum Lstar' (shaLen E) σ hσ P.retained P.D₀_mem ?_ r ?_ 0 C ?_
  · rw [hL' D₀ P.D₀_mem]
    exact hL₀
  · intro D hD
    rw [hL' D hD, hL' D₀ P.D₀_mem]
    exact (hr D hD).2
  · -- (E.9) at a retained `σD`: it is odd and squarefree
    intro h hh
    have hex : ∃ D ∈ P.retained, h = σ * (D : ℤ) := by
      by_contra hne
      exact hh (ite_eq_right hne)
    obtain ⟨D, hD, rfl⟩ := hex
    rw [hL' D hD] at hh ⊢
    obtain ⟨hD0, hsq, hc, -⟩ := P.retained_spec D hD
    have h2N : 2 ∣ P.N := dvd_trans (by norm_num) P.hN
    have hDodd : Odd D := by
      rcases Nat.even_or_odd D with he | ho
      · exfalso
        have h21 : 2 ∣ Nat.gcd D P.N := Nat.dvd_gcd (even_iff_two_dvd.mp he) h2N
        rw [Nat.Coprime.gcd_eq_one hc] at h21
        omega
      · exact ho
    have hodd : Odd (σ * (D : ℤ)) := by
      obtain ⟨k, hk⟩ := hDodd
      rcases hσ with rfl | rfl
      · exact ⟨k, by rw [hk]; push_cast; ring⟩
      · exact ⟨-k - 1, by rw [hk]; push_cast; ring⟩
    have hsqz : Squarefree (σ * (D : ℤ)) := by
      rw [← Int.squarefree_natAbs]
      rcases hσ with rfl | rfl <;> simpa using hsq
    have h9D := hC (σ * D) hodd hsqz hh
    rw [sub_zero]
    exact h9D

end ZInQ.Manuscript.RC.Even
