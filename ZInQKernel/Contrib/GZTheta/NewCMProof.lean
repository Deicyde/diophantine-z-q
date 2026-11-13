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


theorem level_pos_div : 0 < 32 * d ^ 2 / M := by
  have hN : 0 < 32 * d ^ 2 := Nat.pos_of_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero 2 (NeZero.ne d)))
  exact Nat.div_pos (Nat.le_of_dvd hN hMN) (Nat.pos_of_ne_zero (NeZero.ne M))

/-- **The Fricke identity in terms of `g`**: with `κ = −32 d² (−32/d)` and `c_g` the Fricke
constant of `g`, `κ f_d(τ) = c_g ∑_{e ∣ P} c_e (P/e)² g((P/e)τ)`, `P = N/M`. -/
theorem fricke_identity :
    ∃ cg : ℂ, ∀ τ : ℍ, (-32 * (d : ℂ) ^ 2 * jacobiChar d ((-32 : ℤ) : ZMod d)) *
      cmForm etaForm32 d τ = cg * ∑ e ∈ (32 * d ^ 2 / M).divisors,
        cAr M d (coeff g) e * (((32 * d ^ 2 / M / e : ℕ) : ℂ) ^ 2 *
          gAt g.toCuspForm (32 * d ^ 2 / M / e) τ) := by
  obtain ⟨cg, hcg⟩ := newform_fricke g hχ
  refine ⟨cg, fun τ => ?_⟩
  set P := 32 * d ^ 2 / M with hP
  have hMP : M * P = 32 * d ^ 2 := Nat.mul_div_cancel' hMN
  have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
  have hw : 0 < (-1 / (32 * (d : ℂ) ^ 2 * τ)).im := by
    have := fricke32_im_pos (⟨(d : ℂ) ^ 2 * τ, by
      simp only [mul_im, ← Complex.ofReal_natCast, ← Complex.ofReal_pow, ofReal_re, ofReal_im,
        zero_mul, add_zero]
      exact mul_pos (by have := NeZero.ne d; positivity) τ.im_pos⟩ : ℍ)
    simpa [mul_assoc] using this
  have hfr := cmForm_fricke hd4 hsq τ hw
  rw [cmForm_eq_sum hd4 hsq hMN g hχ hgood] at hfr
  -- each term
  have hterm : ∀ e ∈ P.divisors, gAt g.toCuspForm e ⟨-1 / (32 * (d : ℂ) ^ 2 * τ), hw⟩ =
      cg * ((P / e : ℕ) : ℂ) ^ 2 * (τ : ℂ) ^ 2 * gAt g.toCuspForm (P / e) τ := by
    intro e he
    have he0 := Nat.pos_of_mem_divisors he
    have heP : e ∣ P := Nat.dvd_of_mem_divisors he
    have hj : 0 < P / e := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero
      (Nat.ne_of_gt (level_pos_div hd4 hsq hMN g hχ hgood))) heP) he0
    rw [gAt, dif_pos he0, gAt, dif_pos hj]
    have hcast : (M : ℂ) * ((P / e : ℕ) : ℂ) * (e : ℂ) = 32 * (d : ℂ) ^ 2 := by
      have : M * (P / e) * e = 32 * d ^ 2 := by
        rw [mul_assoc, Nat.div_mul_cancel heP, hMP]
      exact_mod_cast this
    have hpt : ((e : ℕ) : ℂ) * ((⟨-1 / (32 * (d : ℂ) ^ 2 * τ), hw⟩ : ℍ) : ℂ) =
        -1 / ((M : ℂ) * (((P / e : ℕ) : ℂ) * τ)) := by
      simp only [UpperHalfPlane.coe_mk]
      have he0' : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
      rw [← hcast]
      field_simp
    have hz' : 0 < (-1 / ((M : ℂ) * (((P / e : ℕ) : ℂ) * τ))).im := by
      rw [← hpt]; exact mul_im_pos_of_nat he0 _
    have := hcg (((P / e : ℕ) : ℂ) * τ) (mul_im_pos_of_nat hj τ) hz'
    rw [show (⟨((e : ℕ) : ℂ) * ((⟨-1 / (32 * (d : ℂ) ^ 2 * τ), hw⟩ : ℍ) : ℂ),
        mul_im_pos_of_nat he0 _⟩ : ℍ) = ⟨-1 / ((M : ℂ) * (((P / e : ℕ) : ℂ) * τ)), hz'⟩ from
      UpperHalfPlane.ext hpt, this]
    ring
  rw [Finset.sum_congr rfl fun e he => by rw [hterm e he]] at hfr
  apply mul_left_cancel₀ (pow_ne_zero 2 hτ0)
  rw [Finset.mul_sum, Finset.mul_sum]
  have : ∀ e ∈ P.divisors, cAr M d (coeff g) e * (cg * ((P / e : ℕ) : ℂ) ^ 2 * (τ : ℂ) ^ 2 *
      gAt g.toCuspForm (P / e) τ) = (τ : ℂ) ^ 2 * (cg * (cAr M d (coeff g) e *
        (((P / e : ℕ) : ℂ) ^ 2 * gAt g.toCuspForm (P / e) τ))) := fun e _ => by ring
  rw [Finset.sum_congr rfl this] at hfr
  linear_combination -hfr


theorem kappa_ne_zero : (-32 * (d : ℂ) ^ 2 * jacobiChar d ((-32 : ℤ) : ZMod d)) ≠ 0 := by
  have hodd : Odd d := odd_of_mod_four hd4
  have h32 : Nat.Coprime 32 d := by
    have : Nat.Coprime (2 ^ 5) d := Nat.Coprime.pow_left 5 (Nat.coprime_two_left.mpr hodd)
    simpa using this
  have hu : IsUnit (((-32 : ℤ) : ZMod d)) := by
    have : IsUnit (((32 : ℕ) : ZMod d)) := (ZMod.isUnit_iff_coprime 32 d).mpr h32
    have h' : ((-32 : ℤ) : ZMod d) = -((32 : ℕ) : ZMod d) := by push_cast; ring
    rw [h']; exact this.neg
  have hsq32 := jacobiChar_sq_unit d hu.unit
  have hχ0 : jacobiChar d ((-32 : ℤ) : ZMod d) ≠ 0 := by
    intro h0; rw [IsUnit.unit_spec, h0] at hsq32; simp at hsq32
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hd0)) hχ0

/-- **The coefficient identity** from the Fricke identity. -/
theorem coeff_identity :
    ∃ cg : ℂ, ∀ m : ℕ, (-32 * (d : ℂ) ^ 2 * jacobiChar d ((-32 : ℤ) : ZMod d)) *
      heckeCoeff d m = cg * ∑ e ∈ (32 * d ^ 2 / M).divisors, cAr M d (coeff g) e *
        (((32 * d ^ 2 / M / e : ℕ) : ℂ) ^ 2 *
          (if 32 * d ^ 2 / M / e ∣ m then coeff g (m / (32 * d ^ 2 / M / e)) else 0)) := by
  obtain ⟨cg, hfi⟩ := fricke_identity hd4 hsq hMN g hχ hgood
  refine ⟨cg, fun m => ?_⟩
  set P := 32 * d ^ 2 / M with hP
  set κ := -32 * (d : ℂ) ^ 2 * jacobiChar d ((-32 : ℤ) : ZMod d) with hκ
  have hκ0 : κ ≠ 0 := kappa_ne_zero hd4 hsq hMN g hχ hgood
  have hjpos : ∀ e ∈ P.divisors, 0 < P / e := fun e he =>
    Nat.div_pos (Nat.le_of_dvd (level_pos_div hd4 hsq hMN g hχ hgood)
      (Nat.dvd_of_mem_divisors he)) (Nat.pos_of_mem_divisors he)
  have key : ∀ τ : ℍ, HasSum (fun m : ℕ => ((cg * ∑ e ∈ P.divisors, cAr M d (coeff g) e *
      (((P / e : ℕ) : ℂ) ^ 2 * (if P / e ∣ m then coeff g (m / (P / e)) else 0))) / κ) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ m) (cmForm etaForm32 d τ) := by
    intro τ
    have hR : HasSum (fun m : ℕ => ∑ e ∈ P.divisors, cAr M d (coeff g) e *
        (((P / e : ℕ) : ℂ) ^ 2 * ((if P / e ∣ m then coeff g (m / (P / e)) else 0) *
          Function.Periodic.qParam 1 (τ : ℂ) ^ m)))
        (∑ e ∈ P.divisors, cAr M d (coeff g) e *
          (((P / e : ℕ) : ℂ) ^ 2 * gAt g.toCuspForm (P / e) τ)) :=
      hasSum_sum fun e he => by
        rw [gAt, dif_pos (hjpos e he)]
        exact ((hasSum_scaled g.toCuspForm (hjpos e he) τ).mul_left _).mul_left _
    have h2 := (hR.mul_left cg).div_const κ
    rw [← hfi τ, mul_div_cancel_left₀ _ hκ0] at h2
    refine h2.congr_fun fun m => ?_
    simp only [smul_eq_mul, Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  have := ModularFormClass.qExpansion_coeff_unique one_pos
    (TauCeti.one_mem_strictPeriods_Gamma1_map _) key m
  rw [qExpansion_cmForm_coeff qExpansion_etaForm32_coeff d m] at this
  rw [← this]
  field_simp

end Ident


/-! ### Evaluating the coefficient identity at `1`, `p`, `p²` -/

theorem sum_divisors_ite_dvd_prime_pow {P : ℕ} (hP : P ≠ 0) {p : ℕ} (hp : p.Prime) (j : ℕ)
    (ψ : ℕ → ℂ) :
    ∑ f ∈ P.divisors, (if f ∣ p ^ j then ψ f else 0) =
      ∑ k ∈ Finset.range (j + 1), (if p ^ k ∣ P then ψ (p ^ k) else 0) := by
  rw [← Nat.sum_divisors_prime_pow (f := fun f => if f ∣ P then ψ f else 0) hp,
    ← Finset.sum_filter, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext f
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, pow_ne_zero _ hp.ne_zero⟩, h1⟩
    · rintro ⟨⟨h1, _⟩, h2⟩; exact ⟨⟨h2, hP⟩, h1⟩
  · intro f _; rfl

/-- Reindexing `e ↦ P/e`. -/
theorem rsum_reindex (P m : ℕ) (hP : P ≠ 0) (c b : ℕ → ℂ) :
    ∑ e ∈ P.divisors, c e * (((P / e : ℕ) : ℂ) ^ 2 * (if P / e ∣ m then b (m / (P / e)) else 0)) =
      ∑ f ∈ P.divisors, (if f ∣ m then c (P / f) * ((f : ℂ) ^ 2 * b (m / f)) else 0) := by
  rw [← Nat.sum_div_divisors P (fun f => if f ∣ m then c (P / f) * ((f : ℂ) ^ 2 * b (m / f))
    else 0)]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [Nat.div_div_self (Nat.dvd_of_mem_divisors he) hP]
  split_ifs <;> ring


theorem factorization_level_two {d : ℕ} [NeZero d] (hodd : Odd d) :
    (32 * d ^ 2).factorization 2 = 5 := by
  have hd0 : d ≠ 0 := NeZero.ne d
  rw [Nat.factorization_mul (by norm_num) (pow_ne_zero 2 hd0), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply]
  have h32 : (32 : ℕ).factorization 2 = 5 := by
    rw [show (32 : ℕ) = 2 ^ 5 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]; simp
  have hd2 : d.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (fun h => by
    obtain ⟨t, ht⟩ := hodd; omega)
  rw [h32, hd2]
  rfl

theorem factorization_level_odd {d : ℕ} [NeZero d] (hsq : Squarefree d) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : p ∣ d) : (32 * d ^ 2).factorization p = 2 := by
  have hd0 : d ≠ 0 := NeZero.ne d
  rw [Nat.factorization_mul (by norm_num) (pow_ne_zero 2 hd0), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply]
  have h32 : (32 : ℕ).factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro h
    have : p ∣ 2 ^ 5 := by norm_num; exact h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this))
  have hd1 : d.factorization p = 1 := by
    have h1 : 1 ≤ d.factorization p := (hp.dvd_iff_one_le_factorization hd0).mp hpd
    have h2 : d.factorization p ≤ 1 := hsq.natFactorization_le_one p
    omega
  rw [h32, hd1]
  rfl

/-- **The level of the newform attached to `f_d` is `32 d²`** (Atkin–Li for `f₁ ⊗ (·/d)`). -/
theorem level_eq_of_assoc {d : ℕ} [NeZero d] (hd4 : d % 4 = 1) (hsq : Squarefree d) {M : ℕ}
    [NeZero M] (hMN : M ∣ 32 * d ^ 2) (g : Newform M 2) (hχ : g.χ = 1)
    (hgood : ∀ p : ℕ, p.Prime → ¬ p ∣ 2 * d → coeff g p = heckeCoeff d p) :
    M = 32 * d ^ 2 := by
  by_contra hne
  have hodd : Odd d := odd_of_mod_four hd4
  set N := 32 * d ^ 2 with hN
  have hN0 : N ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 (NeZero.ne d))
  have hM0 : M ≠ 0 := NeZero.ne M
  set P := N / M with hP
  have hP0 : P ≠ 0 := Nat.ne_of_gt (level_pos_div hd4 hsq hMN g hχ hgood)
  obtain ⟨cg, hci⟩ := coeff_identity hd4 hsq hMN g hχ hgood
  set κ := -32 * (d : ℂ) ^ 2 * jacobiChar d ((-32 : ℤ) : ZMod d) with hκ
  have hκ0 : κ ≠ 0 := kappa_ne_zero hd4 hsq hMN g hχ hgood
  obtain ⟨hmul, hpow⟩ := newform_mul_pow g hχ
  set c := cAr M d (coeff g) with hcdef
  have hcm : c.IsMultiplicative := cAr_mult M d (coeff g)
  have hb1 : coeff g 1 = 1 := g.isNorm
  -- the identity at `p ^ j`
  have hr : ∀ (p : ℕ), p.Prime → ∀ j : ℕ, κ * heckeCoeff d (p ^ j) =
      cg * ∑ k ∈ Finset.range (j + 1), (if p ^ k ∣ P then c (P / p ^ k) *
        (((p ^ k : ℕ) : ℂ) ^ 2 * coeff g (p ^ j / p ^ k)) else 0) := by
    intro p hp j
    rw [hci, rsum_reindex P (p ^ j) hP0 (fun e => c e) (coeff g),
      sum_divisors_ite_dvd_prime_pow hP0 hp j]
  -- `κ = cg c(P)`
  have hr1 : κ = cg * c P := by
    have := hr 2 Nat.prime_two 0
    simp only [pow_zero, heckeCoeff_one, mul_one, zero_add, Finset.range_one,
      Finset.sum_singleton, one_dvd, if_true, Nat.div_one, Nat.cast_one, one_pow, one_mul,
      Nat.div_self Nat.one_pos, hb1] at this
    exact this
  have hcP : c P ≠ 0 := fun h0 => hκ0 (by rw [hr1, h0, mul_zero])
  have hcg : cg ≠ 0 := fun h0 => hκ0 (by rw [hr1, h0, zero_mul])
  -- a prime where `M` falls short
  obtain ⟨p, hpM⟩ : ∃ p, M.factorization p < N.factorization p := by
    by_contra h
    simp only [not_exists, not_lt] at h
    apply hne
    apply Nat.eq_of_factorization_eq hM0 hN0
    intro p
    exact le_antisymm ((Nat.factorization_le_iff_dvd hM0 hN0).mpr hMN p) (h p)
  have hp : p.Prime := by
    by_contra hnp
    rw [Nat.factorization_eq_zero_of_not_prime N hnp] at hpM
    omega
  have hpN : p ∣ N := (hp.dvd_iff_one_le_factorization hN0).mpr (by omega)
  have hp2d : p ∣ 2 * d := (dvd_two_mul_iff_not_coprime hp).mpr fun hc =>
    (Nat.Prime.coprime_iff_not_dvd hp).mp hc hpN
  set v := P.factorization p with hv
  have hvP : v = N.factorization p - M.factorization p := by
    rw [hv, hP, Nat.factorization_div hMN]; rfl
  set Q := P / p ^ v with hQ
  have hPQ : p ^ v * Q = P := Nat.ordProj_mul_ordCompl_eq_self P p
  have hcopQ : Nat.Coprime p Q := Nat.coprime_ordCompl hp hP0
  have hcPv : ∀ k, c (p ^ k * Q) = c (p ^ k) * c Q := fun k =>
    hcm.map_mul_of_coprime (Nat.Coprime.pow_left k hcopQ)
  have hloc : ∀ k, c (p ^ k) = locC M d (coeff g) p k := fun k => cAr_prime_pow hp k
  have hApk : ∀ k, 1 ≤ k → heckeCoeff d (p ^ k) = 0 := fun k hk =>
    heckeCoeff_pow_of_dvd_two_mul hd4 hp hp2d hk
  by_cases hp2 : p = 2
  · -- `p = 2`: `c(2^v) = 0`
    subst hp2
    have h5 : N.factorization 2 = 5 := factorization_level_two hodd
    have hv1 : 1 ≤ v := by omega
    have hc0 : c (2 ^ v) = 0 := by
      rw [hloc]
      unfold locC
      rw [if_neg (by omega), if_pos hp2d]
      by_cases hv1' : v = 1
      · rw [if_pos hv1', neg_eq_zero]
        have h4 : 2 ^ 2 ∣ M := (Nat.prime_two.pow_dvd_iff_le_factorization hM0).mpr (by omega)
        exact Newform.qExpansion_coeff_prime_eq_zero_of_sq_dvd g Nat.prime_two h4
          (dirichletLift_factorsThrough_of_one g hχ _ (Nat.div_dvd_of_dvd
            ((dvd_pow_self 2 two_ne_zero).trans h4)))
      · rw [if_neg hv1']
        split_ifs with h2
        · exfalso
          apply h2.2
          exact (Nat.prime_two.dvd_iff_one_le_factorization hM0).mpr (by omega)
        · rfl
    apply hcP
    rw [← hPQ, hcPv, hc0, zero_mul]
  · -- odd `p ∣ d`
    have hpd : p ∣ d := by
      rcases (Nat.Prime.dvd_mul hp).mp hp2d with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h) hp2
      · exact h
    have hNp : N.factorization p = 2 := factorization_level_odd hsq hp hp2 hpd
    have hcQ : cg * c Q ≠ 0 := by
      intro h0
      apply hcP
      rw [← hPQ, hcPv]
      have : c Q = 0 := (mul_eq_zero.mp h0).resolve_left hcg
      rw [this, mul_zero]
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hp1 : (p : ℂ) ^ 2 ≠ 1 := by
      intro h
      have : (p : ℕ) ^ 2 = 1 := by exact_mod_cast h
      have := hp.one_lt
      nlinarith
    have hrp := hr p hp 1
    rw [hApk 1 le_rfl, mul_zero, Finset.sum_range_succ, Finset.sum_range_one] at hrp
    simp only [pow_zero, one_dvd, if_true, Nat.div_one, pow_one, Nat.cast_one, one_pow, one_mul,
      Nat.div_self hp.pos, hb1] at hrp
    by_cases hv2 : v = 2
    · -- `p ∤ M`
      have hpM0 : M.factorization p = 0 := by omega
      have hpnM : ¬ p ∣ M := fun h =>
        absurd ((hp.dvd_iff_one_le_factorization hM0).mp h) (by omega)
      have hP' : P = p ^ 2 * Q := by rw [← hPQ, hv2]
      have hPp : P / p = p * Q := by rw [hP', show p ^ 2 * Q = p * (p * Q) by ring,
        Nat.mul_div_cancel_left _ hp.pos]
      have hPp2 : P / p ^ 2 = Q := by rw [hP', Nat.mul_div_cancel_left _ (pow_pos hp.pos 2)]
      have hcp : c p = -coeff g p := by
        have := hloc 1; rw [pow_one] at this; rw [this]; simp [locC, hp2d]
      have hcp2 : c (p ^ 2) = p := by rw [hloc]; simp [locC, hp2d, hpnM]
      have hdivp : p ∣ P := by rw [hP']; exact Dvd.intro (p * Q) (by ring)
      rw [if_pos hdivp, hPp, show p * Q = p ^ 1 * Q by ring, hcPv, pow_one, hcp,
        hP', hcPv, hcp2] at hrp
      -- `b_p = 0`
      have hbp : coeff g p = 0 := by
        have : cg * c Q * (coeff g p * ((p : ℂ) - (p : ℂ) ^ 2)) = 0 := by linear_combination -hrp
        have h' := (mul_eq_zero.mp this).resolve_left hcQ
        have hne' : (p : ℂ) - (p : ℂ) ^ 2 ≠ 0 := by
          intro h0
          have : (p : ℂ) * (1 - p) = 0 := by linear_combination h0
          rcases mul_eq_zero.mp this with h | h
          · exact hp0 h
          · apply hp1; have : (p : ℂ) = 1 := by linear_combination -h
            rw [this]; norm_num
        exact (mul_eq_zero.mp h').resolve_right hne'
      -- the identity at `p²`
      have hrp2 := hr p hp 2
      rw [hApk 2 (by norm_num), mul_zero, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_one] at hrp2
      have hdivp2 : p ^ 2 ∣ P := by rw [hP']; exact Dvd.intro Q rfl
      simp only [pow_zero, one_dvd, if_true, Nat.div_one, pow_one, Nat.cast_one, one_pow,
        one_mul, if_pos hdivp, if_pos hdivp2, Nat.div_self (pow_pos hp.pos 2)] at hrp2
      have hbp2 : coeff g (p ^ 2) = -p := by
        have := hpow p hp 0
        simp only [zero_add, pow_one, pow_zero, if_neg hpnM] at this
        rw [this, hbp, hb1]; ring
      rw [show p ^ 2 / p = p by rw [pow_two, Nat.mul_div_cancel _ hp.pos], hbp, hbp2,
        hPp, show p * Q = p ^ 1 * Q by ring, hcPv, pow_one, hcp, hPp2, hP', hcPv, hcp2] at hrp2
      push_cast at hrp2
      have : cg * c Q * ((p : ℂ) ^ 2 * ((p : ℂ) ^ 2 - 1)) = 0 := by
        linear_combination -hrp2 - (cg * c Q * (p : ℂ) ^ 4) * hb1
      rcases mul_eq_zero.mp this with h | h
      · exact hcQ h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact pow_ne_zero 2 hp0 h'
        · exact hp1 (by linear_combination h')
    · -- `p ∥ M`
      have hv1 : v = 1 := by omega
      have hpM1 : M.factorization p = 1 := by omega
      have hpdvdM : p ∣ M := (hp.dvd_iff_one_le_factorization hM0).mpr (by omega)
      have hpsq : ¬ p ^ 2 ∣ M := fun h =>
        absurd ((hp.pow_dvd_iff_le_factorization hM0).mp h) (by omega)
      have hex := TauCeti.Nat.IsExactDivisor.of_not_sq_dvd hp hpdvdM hpsq
      have hbp2 : coeff g p ^ 2 = 1 := by
        have := Newform.qExpansion_coeff_prime_sq_of_isExactDivisor g hp hex
          (χ₀ := 1) (by rw [hχ, MonoidHom.one_comp])
        rw [MonoidHom.one_apply, Units.val_one, one_mul, sub_self, zpow_zero] at this
        exact this
      have hP' : P = p * Q := by rw [← hPQ, hv1, pow_one]
      have hPp : P / p = Q := by rw [hP', Nat.mul_div_cancel_left _ hp.pos]
      have hcp : c p = -coeff g p := by
        have := hloc 1; rw [pow_one] at this; rw [this]; simp [locC, hp2d]
      have hdivp : p ∣ P := by rw [hP']; exact Dvd.intro Q rfl
      rw [if_pos hdivp, hPp, hP', show p * Q = p ^ 1 * Q by ring, hcPv, pow_one, hcp] at hrp
      have : cg * c Q * ((p : ℂ) ^ 2 - coeff g p ^ 2) = 0 := by linear_combination -hrp
      rw [hbp2] at this
      rcases mul_eq_zero.mp this with h | h
      · exact hcQ h
      · exact hp1 (by linear_combination h)

end ZInQ.GZTheta
