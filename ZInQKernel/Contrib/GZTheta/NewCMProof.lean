import ZInQKernel.Contrib.GZTheta.TwistFricke
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.AtkinLehner

/-!
# gz-theta: the twists `f_d` are new at level `32 d²`

Let `g` be the newform attached to `f_d` (Tau Ceti, Diamond–Shurman 5.8.4), of level `M ∣ N`,
`N = 32 d²`, with coefficients `b_n`. Then `f_d = ∑_{e ∣ N/M} c_e g(e τ)` where `c` is the
multiplicative function with local factors `1 − b_p X + [p ∤ M] p X²` at `p ∣ 2d`
(`heckeCoeff d = c ⋆ b`, Dirichlet convolution). The Fricke involutions
`f_d(−1/(Nτ)) = κ τ² f_d(τ)` (`cmForm_fricke`) and `g(−1/(Mτ)) = c_g τ² g(τ)` give
`κ f_d(τ) = c_g ∑_e c_e (N/(Me))² g((N/(Me))τ)`; comparing the coefficients of `q`, `q^p`,
`q^{p²}` forces `M = N`. This is Atkin–Li's theorem for the family `f₁ ⊗ (·/d)`.
-/

open Complex Filter ModularForm CongruenceSubgroup HeckeRing.GL2 Matrix.SpecialLinearGroup
  ArithmeticFunction
open UpperHalfPlane hiding I
open scoped Real Topology MatrixGroups

noncomputable section

namespace ZInQ.GZTheta

open ZInQ.Contrib.HeckeFE ZInQ.GZDecomp

/-! ### The arithmetic functions -/

/-- The local factor of `c` at `p`: `1 − b_p X + [p ∤ M] p X²` if `p ∣ 2d`, else `1`. -/
def locC (M d : ℕ) (b : ℕ → ℂ) (p j : ℕ) : ℂ :=
  if j = 0 then 1
  else if p ∣ 2 * d then (if j = 1 then -b p else if j = 2 ∧ ¬ p ∣ M then (p : ℂ) else 0)
  else 0

/-- The multiplicative function `c` with local factors `locC`. -/
def cAr (M d : ℕ) (b : ℕ → ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod (locC M d b), by simp⟩

theorem cAr_apply {M d : ℕ} {b : ℕ → ℂ} {n : ℕ} (hn : n ≠ 0) :
    cAr M d b n = n.factorization.prod (locC M d b) := by
  show (if n = 0 then 0 else _) = _
  rw [if_neg hn]

theorem cAr_mult (M d : ℕ) (b : ℕ → ℂ) : (cAr M d b).IsMultiplicative := by
  refine ⟨by rw [cAr_apply one_ne_zero]; simp, fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [cAr_apply (mul_ne_zero hm hn), cAr_apply hm, cAr_apply hn,
    Nat.factorization_mul_of_coprime hmn]
  refine Finsupp.prod_add_index_of_disjoint ?_ _
  rw [Nat.support_factorization, Nat.support_factorization]
  exact hmn.disjoint_primeFactors

theorem cAr_prime_pow {M d : ℕ} {b : ℕ → ℂ} {p : ℕ} (hp : p.Prime) (j : ℕ) :
    cAr M d b (p ^ j) = locC M d b p j := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · rw [pow_zero, cAr_apply one_ne_zero]; simp [locC]
  rw [cAr_apply (pow_ne_zero _ hp.ne_zero), hp.factorization_pow, Finsupp.prod_single_index]
  simp [locC]

/-- The coefficients of `heckeCoeff d` as an arithmetic function. -/
def AAr (d : ℕ) : ArithmeticFunction ℂ := ⟨fun n => heckeCoeff d n, heckeCoeff_zero d⟩

theorem AAr_mult (d : ℕ) : (AAr d).IsMultiplicative :=
  ⟨heckeCoeff_one d, fun {m n} h => heckeMult d m n h⟩

/-- The coefficients of a newform as an arithmetic function. -/
def bAr {M : ℕ} [NeZero M] (g : Newform M 2) : ArithmeticFunction ℂ :=
  ⟨fun n => coeff g n, CuspFormClass.qExpansion_coeff_zero _ one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map M)⟩

theorem bAr_apply {M : ℕ} [NeZero M] (g : Newform M 2) (n : ℕ) : bAr g n = coeff g n := rfl


/-! ### `heckeCoeff d = c ⋆ b` -/

section Conv

variable {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) {M : ℕ} [NeZero M]
  (hMN : M ∣ 32 * d ^ 2) (g : Newform M 2) (hχ : g.χ = 1)
  (hgood : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * d → coeff g p = heckeCoeff d p)
include hMN hχ

omit [NeZero d] [NeZero M] hχ in
theorem dvd_two_mul_of_dvd_level {p : ℕ} (hp : p.Prime) (hpM : p ∣ M) : p ∣ 2 * d :=
  (dvd_two_mul_iff_not_coprime hp).mpr fun hc =>
    (Nat.Prime.coprime_iff_not_dvd hp).mp hc (hpM.trans hMN)

omit [NeZero d] hMN in
/-- The coefficient facts of `g`. -/
theorem newform_mul_pow :
    (∀ u v : ℕ, Nat.Coprime u v → coeff g (u * v) = coeff g u * coeff g v) ∧
    ∀ (p : ℕ), p.Prime → ∀ r : ℕ, coeff g (p ^ (r + 2)) =
      coeff g p * coeff g (p ^ (r + 1)) - (if p ∣ M then 0 else (p : ℂ)) * coeff g (p ^ r) := by
  obtain ⟨hmul, hpow⟩ :=
    (Eigenform.exists_toCuspForm_eq_and_χ_eq_iff_qExpansion_coeff_mul_and_prime_pow_add_two
      g.mem_charSpace g.isNorm).mp ⟨g.toEigenform, g.toEigenform_toCuspForm, g.toEigenform_χ⟩
  refine ⟨hmul, fun p hp r => ?_⟩
  have e := hpow p hp r
  have hχp : (MulChar.ofUnitHom g.χ : DirichletCharacter ℂ M) p * (p : ℂ) ^ ((2 : ℤ) - 1) =
      if p ∣ M then 0 else (p : ℂ) := by
    split_ifs with h
    · rw [MulChar.map_nonunit _ (by
        rw [ZMod.isUnit_iff_coprime, Nat.Prime.coprime_iff_not_dvd hp, not_not]; exact h), zero_mul]
    · have hc : Nat.Coprime p M := (Nat.Prime.coprime_iff_not_dvd hp).mpr h
      rw [← ZMod.coe_unitOfCoprime p hc, MulChar.ofUnitHom_coe, hχ]
      simp
  rw [hχp] at e
  exact e

theorem bAr_mult : (bAr g).IsMultiplicative :=
  ⟨g.isNorm, fun {u v} h => (newform_mul_pow g hχ).1 u v h⟩

include hd4 hsq hgood in
/-- At the good primes the coefficients of `g` are those of `heckeCoeff d`. -/
theorem coeff_good_pow {p : ℕ} (hp : p.Prime) (hp2d : ¬ p ∣ 2 * d) (k : ℕ) :
    coeff g (p ^ k) = heckeCoeff d (p ^ k) := by
  have hpow := (newform_mul_pow g hχ).2
  have hpM : ¬ p ∣ M := fun h => hp2d (dvd_two_mul_of_dvd_level hMN hp h)
  have h1 := hgood p hp hp2d
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp only [pow_zero]; rw [heckeCoeff_one]; exact g.isNorm
    | 1, _ => simpa using h1
    | r + 2, ih =>
      rw [hpow p hp r, if_neg hpM, heckePrimePow' hd4 hsq p hp r, if_neg hp2d, h1,
        ih (r + 1) (by omega), ih r (by omega)]

include hd4 hsq hgood in
/-- **`heckeCoeff d = c ⋆ b`.** -/
theorem AAr_eq_mul : AAr d = cAr M d (coeff g) * bAr g := by
  have hpow := (newform_mul_pow g hχ).2
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (AAr_mult d) _
    ((cAr_mult M d (coeff g)).mul (bAr_mult hMN g hχ))).mpr fun p i hp => ?_
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun x y => cAr M d (coeff g) x * bAr g y), Nat.sum_divisors_prime_pow hp]
  simp only [cAr_prime_pow hp, bAr_apply]
  have hb1 : coeff g 1 = 1 := g.isNorm
  have hsub : ∀ k ∈ Finset.range (i + 1), p ^ i / p ^ k = p ^ (i - k) := fun k hk =>
    Nat.pow_div (by simpa [Nat.lt_succ_iff] using hk) hp.pos
  rw [Finset.sum_congr rfl fun k hk => by rw [hsub k hk]]
  show heckeCoeff d (p ^ i) = _
  by_cases hp2d : p ∣ 2 * d
  · -- bad prime: both sides are `[i = 0]`
    match i with
    | 0 => simp [locC, heckeCoeff_one, hb1]
    | 1 =>
      rw [show p ^ 1 = p from pow_one p, ← pow_one p,
        heckeCoeff_pow_of_dvd_two_mul hd4 hp hp2d le_rfl]
      simp [Finset.sum_range_succ, locC, hp2d, hb1]
    | r + 2 =>
      rw [heckeCoeff_pow_of_dvd_two_mul hd4 hp hp2d (by omega)]
      rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ']
      have hz : ∀ k ∈ Finset.range r, locC M d (coeff g) p (k + 1 + 1 + 1) *
          coeff g (p ^ (r + 2 - (k + 1 + 1 + 1))) = 0 := fun k _ => by
        simp [locC]
      rw [Finset.sum_eq_zero hz]
      simp only [locC, if_pos hp2d]
      norm_num
      rw [hpow p hp r]
      by_cases hpM : p ∣ M
      · simp [hpM, hb1]
      · simp [hpM, hb1]; ring
  · -- good prime: `c` is trivial at `p`
    rw [Finset.sum_eq_single 0]
    · simp [locC, coeff_good_pow hd4 hsq hMN g hχ hgood hp hp2d i]
    · intro k _ hk; simp [locC, hk, hp2d]
    · intro h; simp at h


omit [NeZero M] hMN hχ in
include hd4 hsq in
/-- `v_p(32 d²) ≥ 2` for `p ∣ 2d`. -/
theorem two_le_factorization_level {p : ℕ} (hp : p.Prime) (h : p ∣ 2 * d) :
    2 ≤ (32 * d ^ 2).factorization p := by
  have hN : 32 * d ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 (NeZero.ne d))
  rw [← hp.pow_dvd_iff_le_factorization hN]
  rcases (Nat.Prime.dvd_mul hp).mp h with h2 | hd
  · have : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
    subst this
    exact Dvd.dvd.mul_right (by norm_num : 2 ^ 2 ∣ 32) _
  · exact Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hd 2) _

omit [NeZero d] hMN hχ in
theorem dirichletLift_factorsThrough_of_one (hχ' : g.χ = 1) (q : ℕ) (hq : q ∣ M) :
    g.dirichletLift.FactorsThrough q :=
  ⟨hq, 1, by rw [dirichletLift_eq_one g hχ', DirichletCharacter.changeLevel_one]⟩

include hd4 hsq in
/-- **The support of `c`**: `c x ≠ 0 ⇒ x ∣ N/M`. -/
theorem dvd_of_cAr_ne_zero {x : ℕ} (hx : cAr M d (coeff g) x ≠ 0) : x ∣ 32 * d ^ 2 / M := by
  have hN : 32 * d ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 (NeZero.ne d))
  have hM0 : M ≠ 0 := NeZero.ne M
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hP0 : 32 * d ^ 2 / M ≠ 0 := by
    intro h0
    rw [Nat.div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact hM0 h0
    · exact absurd (Nat.le_of_dvd (by positivity) hMN) (by omega)
  rw [← Nat.factorization_le_iff_dvd hx0 hP0, Nat.factorization_div hMN]
  intro p
  rw [cAr_apply hx0, Finsupp.prod, Finset.prod_ne_zero_iff] at hx
  simp only [Finsupp.coe_tsub, Pi.sub_apply]
  by_cases hpx : p ∈ x.factorization.support
  · have hloc := hx p hpx
    have hp : p.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization x ▸ hpx)
    have hxp : x.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hpx
    unfold locC at hloc
    rw [if_neg hxp] at hloc
    by_cases hp2d : p ∣ 2 * d
    · rw [if_pos hp2d] at hloc
      have h2N := two_le_factorization_level hd4 hsq hp hp2d
      by_cases h1 : x.factorization p = 1
      · rw [if_pos h1] at hloc
        -- `b_p ≠ 0`, so `p² ∤ M`
        have hMp : M.factorization p < (32 * d ^ 2).factorization p := by
          by_contra hle
          rw [not_lt] at hle
          apply hloc
          have hsq' : p ^ 2 ∣ M := (hp.pow_dvd_iff_le_factorization hM0).mpr (h2N.trans hle)
          rw [neg_eq_zero]
          exact Newform.qExpansion_coeff_prime_eq_zero_of_sq_dvd g hp hsq'
            (dirichletLift_factorsThrough_of_one g hχ _ (Nat.div_dvd_of_dvd
              ((dvd_pow_self p two_ne_zero).trans hsq')))
        omega
      · rw [if_neg h1] at hloc
        split_ifs at hloc with h2
        · have hM0p : M.factorization p = 0 :=
            Nat.factorization_eq_zero_of_not_dvd h2.2
          omega
        · exact absurd rfl hloc
    · rw [if_neg hp2d] at hloc; exact absurd rfl hloc
  · rw [Finsupp.notMem_support_iff.mp hpx]; exact Nat.zero_le _


end Conv

/-! ### `f_d = ∑_{e ∣ N/M} c_e g(eτ)` -/

theorem qParam_mul_nat (j : ℕ) (τ : ℂ) :
    Function.Periodic.qParam 1 ((j : ℂ) * τ) = Function.Periodic.qParam 1 τ ^ j := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

/-- `G(jτ)` (and `0` for `j = 0`). -/
def gAt {M : ℕ} [NeZero M] (G : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) (j : ℕ) (τ : ℍ) : ℂ :=
  if h : 0 < j then G ⟨(j : ℂ) * τ, mul_im_pos_of_nat h τ⟩ else 0

/-- The `q`-expansion of `G(jτ)`, indexed by the powers of `q`. -/
theorem hasSum_scaled {M : ℕ} [NeZero M] (G : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2) {j : ℕ}
    (hj : 0 < j) (τ : ℍ) :
    HasSum (fun m : ℕ => (if j ∣ m then (qExpansion 1 G).coeff (m / j) else 0) *
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (G ⟨(j : ℂ) * τ, mul_im_pos_of_nat hj τ⟩) := by
  have hG := ModularForm.hasSum_qExpansion G one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map M)
    ⟨(j : ℂ) * τ, mul_im_pos_of_nat hj τ⟩
  simp only [UpperHalfPlane.coe_mk, qParam_mul_nat, ← pow_mul] at hG
  rw [← (Function.Injective.hasSum_iff (g := fun n : ℕ => j * n)
    (fun a b h => Nat.eq_of_mul_eq_mul_left hj h) (fun m hm => ?_))]
  · refine hG.congr_fun fun n => ?_
    simp only [Function.comp_apply, dvd_mul_right, if_true, Nat.mul_div_cancel_left n hj]
  · rw [if_neg, zero_mul]
    rintro ⟨k, rfl⟩
    exact hm ⟨k, rfl⟩


section Ident

variable {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) {M : ℕ} [NeZero M]
  (hMN : M ∣ 32 * d ^ 2) (g : Newform M 2) (hχ : g.χ = 1)
  (hgood : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * d → coeff g p = heckeCoeff d p)
include hd4 hsq hMN hχ hgood

theorem pos_of_mem_divisors' {P e : ℕ} (he : e ∈ P.divisors) : 0 < e :=
  Nat.pos_of_mem_divisors he

/-- The Dirichlet convolution, restricted to the divisors of `N/M`. -/
theorem heckeCoeff_eq_sum_divisors (m : ℕ) :
    heckeCoeff d m = ∑ e ∈ (32 * d ^ 2 / M).divisors,
      cAr M d (coeff g) e * (if e ∣ m then coeff g (m / e) else 0) := by
  set P := 32 * d ^ 2 / M with hP
  have hb0 : coeff g 0 = 0 := CuspFormClass.qExpansion_coeff_zero _ one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map M)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [heckeCoeff_zero, hb0]
  have hA := congrArg (fun f : ArithmeticFunction ℂ => f m) (AAr_eq_mul hd4 hsq hMN g hχ hgood)
  change heckeCoeff d m = _ at hA
  rw [hA, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun x y => cAr M d (coeff g) x * bAr g y)]
  simp only [bAr_apply]
  have hP0 : P ≠ 0 := by
    intro h0
    rw [hP, Nat.div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact NeZero.ne M h0
    · exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero (mul_ne_zero (by norm_num)
        (pow_ne_zero 2 (NeZero.ne d)))) hMN) (by omega)
  -- both sides are the sum over the common divisors of `m` and `P`
  rw [← Finset.sum_filter_add_sum_filter_not m.divisors (· ∣ P)]
  rw [Finset.sum_eq_zero (s := m.divisors.filter (fun x => ¬ x ∣ P)) (fun x hx => by
    simp only [Finset.mem_filter] at hx
    by_contra hne
    exact hx.2 (dvd_of_cAr_ne_zero hd4 hsq hMN g hχ (left_ne_zero_of_mul hne))), add_zero]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext e
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, hP0⟩, h1⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, hm.ne'⟩, h1⟩
  · intro x _; rfl

/-- **`f_d(τ) = ∑_{e ∣ N/M} c_e g(eτ)`.** -/
theorem cmForm_eq_sum (τ : ℍ) :
    cmForm etaForm32 d τ = ∑ e ∈ (32 * d ^ 2 / M).divisors,
      cAr M d (coeff g) e * gAt g.toCuspForm e τ := by
  have hF := ModularForm.hasSum_qExpansion (cmForm etaForm32 d) one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map _) τ
  have hc : ∀ n, (qExpansion 1 (cmForm etaForm32 d)).coeff n = heckeCoeff d n :=
    qExpansion_cmForm_coeff qExpansion_etaForm32_coeff d
  simp only [hc] at hF
  have hR : HasSum (fun m : ℕ => ∑ e ∈ (32 * d ^ 2 / M).divisors,
      cAr M d (coeff g) e * ((if e ∣ m then coeff g (m / e) else 0) *
        Function.Periodic.qParam 1 (τ : ℂ) ^ m))
      (∑ e ∈ (32 * d ^ 2 / M).divisors, cAr M d (coeff g) e * gAt g.toCuspForm e τ) :=
    hasSum_sum fun e he => by
      rw [gAt, dif_pos (Nat.pos_of_mem_divisors he)]
      exact (hasSum_scaled g.toCuspForm (Nat.pos_of_mem_divisors he) τ).mul_left _
  refine hF.unique (hR.congr_fun fun m => ?_)
  rw [heckeCoeff_eq_sum_divisors hd4 hsq hMN g hχ hgood m, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

end Ident

end ZInQ.GZTheta
