import ZInQKernel.Contrib.GZTheta.Split
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Newforms.BadPrime.Vanishing

/-!
# gz-theta: `η(4τ)²η(8τ)²` is new at level 32

The associated newform `g` of `f₁ = η(4τ)²η(8τ)²` (Tau Ceti, Diamond–Shurman 5.8.4) has level
`M ∣ 32`. If `M = 32` then `f₁ = g` (Diamond–Shurman 5.8.2) is new. Otherwise:
* `M = 1` is impossible (`S₂(SL₂(ℤ)) = 0`, Mathlib);
* for `M ∈ {2, 4, 8, 16}`, `f₁(τ) = g(τ) − a₂(g) g(2τ)` (the coefficients agree at odd `n`, and
  `a_{2n}(g) = a₂(g) a_n(g)`); applying the Fricke involution `τ ↦ −1/(32τ)`, under which
  `f₁(−1/(32τ)) = −32 τ² f₁(τ)` while `g(−1/(Mτ)) = c τ² g(τ)`, gives
  `−32 f₁(τ) = c (32/M)² g((32/M)τ) − a₂ c (16/M)² g((16/M)τ)`; dividing by `q` and letting
  `Im τ → ∞`, the left side tends to `−32` and the right side to `0` (for `M = 16`, `a₂(g) = 0`
  because `4 ∣ 16`: Tau Ceti, Miyake 4.6.17).
-/

open Complex Filter ModularForm CongruenceSubgroup HeckeRing.GL2
  Matrix.SpecialLinearGroup
open UpperHalfPlane hiding I
open scoped Real Topology MatrixGroups

noncomputable section

namespace ZInQ.GZTheta

open ZInQ.Contrib.HeckeFE ZInQ.GZDecomp

/-! ### The Fricke involution on `f₁` -/

/-- `f₁(z) = η(4z)² η(8z)²` on `ℂ`. -/
def F₁ (z : ℂ) : ℂ := η (4 * z) ^ 2 * η (8 * z) ^ 2

theorem F₁_fricke {z : ℂ} (hz : 0 < z.im) : F₁ (-1 / (32 * z)) = -32 * z ^ 2 * F₁ z := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h8 : 0 < (8 * z).im := by simp; exact hz
  have h4 : 0 < (4 * z).im := by simp; exact hz
  unfold F₁
  rw [show 4 * (-1 / (32 * z)) = -1 / (8 * z) by field_simp; ring,
    show 8 * (-1 / (32 * z)) = -1 / (4 * z) by field_simp; ring,
    eta_sq_neg_inv h8, eta_sq_neg_inv h4]
  ring_nf
  rw [I_sq]
  ring

/-! ### The Fricke involution on a newform -/

theorem newform_fricke {M : ℕ} [NeZero M] (g : Newform M 2) (hχ : g.χ = 1) :
    ∃ c : ℂ, ∀ (z : ℂ) (hz : 0 < z.im) (hz' : 0 < (-1 / ((M : ℂ) * z)).im),
      g.toCuspForm ⟨-1 / ((M : ℂ) * z), hz'⟩ = c * z ^ 2 * g.toCuspForm ⟨z, hz⟩ := by
  have hfr := g.normalizedFrickeOperatorCusp_eq_frickeSign_smul hχ
  set ε := g.frickeSign hχ
  have hnorm : TauCeti.atkinLehnerNormalizer M 2 = 1 := by
    simp [TauCeti.atkinLehnerNormalizer]
  have hM0 : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  refine ⟨ε * M, fun z hz hz' => ?_⟩
  have h := congrArg (fun F : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2 => (⇑F) ⟨z, hz⟩) hfr
  simp only [TauCeti.coe_normalizedFrickeOperatorCusp, hnorm, one_smul] at h
  rw [ModularForm.slash_apply] at h
  have hdet : (0 : ℝ) < ((TauCeti.frickeGL ℝ M).det : ℝ) := TauCeti.val_det_frickeGL_pos
  have hσ : ∀ w : ℂ, σ (TauCeti.frickeGL ℝ M) w = w := fun w => by
    simp only [σ, if_pos hdet]; rfl
  have hpt : (TauCeti.frickeGL ℝ M • (⟨z, hz⟩ : ℍ)) = ⟨-1 / ((M : ℂ) * z), hz'⟩ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdet, UpperHalfPlane.num, UpperHalfPlane.denom,
      TauCeti.coe_frickeGL]
    simp
  have hden : denom (TauCeti.frickeGL ℝ M) (⟨z, hz⟩ : ℍ) = (M : ℂ) * z := by
    rw [UpperHalfPlane.denom, TauCeti.coe_frickeGL]
    simp
  have hdetv : |((TauCeti.frickeGL ℝ M).det : ℝ)| = M := by
    rw [TauCeti.val_det_frickeGL, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [hσ, hpt, hden, hdetv, CuspForm.smul_apply, smul_eq_mul] at h
  have hz0 : z ≠ 0 := fun h0 => by simp [h0] at hz
  generalize g.toCuspForm ⟨-1 / ((M : ℂ) * z), hz'⟩ = A at h ⊢
  generalize g.toCuspForm ⟨z, hz⟩ = B at h ⊢
  push_cast at h
  have hne : ((M : ℂ) * z) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero hM0 hz0)
  simp only [zpow_one, zpow_neg, zpow_two] at h
  field_simp at h
  linear_combination h


/-! ### The coefficients of the associated newform -/

theorem heckeCoeff_one_even (m : ℕ) : heckeCoeff 1 (2 * m) = 0 := by
  rw [heckeCoeff_one_eq_sum_Soe]
  refine Finset.sum_eq_zero fun p hp => ?_
  exfalso
  simp only [Soe, Finset.mem_filter, mem_normFiber] at hp
  obtain ⟨h1, h2, h3⟩ := hp
  have : (p.1 ^ 2 + p.2 ^ 2) % 2 = 1 := by
    have e1 : p.1 ^ 2 % 2 = 1 := by
      rw [pow_two, Int.mul_emod, h2]; norm_num
    have e2 : p.2 ^ 2 % 2 = 0 := by
      rw [pow_two, Int.mul_emod, h3]; norm_num
    omega
  push_cast at h1
  omega

/-- The coefficient facts for a normalized trivial-character newform `g` of level `M ∣ 16`,
`2 ∣ M`, whose eigenvalues at the odd primes are `heckeCoeff 1 p`. -/
theorem coeff_newform_odd_even {M : ℕ} [NeZero M] (hM16 : M ∣ 16) (hM2 : 2 ∣ M)
    (g : Newform M 2) (hχ : g.χ = 1)
    (hgood : ∀ p : ℕ, p.Prime → p ≠ 2 → coeff g p = heckeCoeff 1 p) :
    (∀ n : ℕ, n % 2 = 1 → coeff g n = heckeCoeff 1 n) ∧
      ∀ n : ℕ, coeff g (2 * n) = coeff g 2 * coeff g n := by
  obtain ⟨hmul, hpow⟩ :=
    (Eigenform.exists_toCuspForm_eq_and_χ_eq_iff_qExpansion_coeff_mul_and_prime_pow_add_two
      g.mem_charSpace g.isNorm).mp ⟨g.toEigenform, g.toEigenform_toCuspForm, g.toEigenform_χ⟩
  have hcopM : ∀ p : ℕ, p.Prime → p ≠ 2 → Nat.Coprime p M := by
    intro p hp hp2
    have h16 : Nat.Coprime p 16 := by
      have : Nat.Coprime p (2 ^ 4) := Nat.Coprime.pow_right 4
        ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      simpa using this
    exact h16.coprime_dvd_right hM16
  have hχp : ∀ p : ℕ, (MulChar.ofUnitHom g.χ : DirichletCharacter ℂ M) p =
      if Nat.Coprime p M then 1 else 0 := by
    intro p
    split_ifs with hc
    · rw [← ZMod.coe_unitOfCoprime p hc, MulChar.ofUnitHom_coe, hχ]; simp
    · exact MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
  -- odd prime powers
  have hpp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ k : ℕ, coeff g (p ^ k) = heckeCoeff 1 (p ^ k) := by
    intro p hp hp2
    have h1 := hgood p hp hp2
    have hp2' : ¬ p ∣ 2 * 1 := by
      rw [mul_one]; intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      match k, ih with
      | 0, _ => simp only [pow_zero]; rw [heckeCoeff_one]; exact g.isNorm
      | 1, _ => simpa using h1
      | r + 2, ih =>
        have e := hpow p hp r
        rw [hχp, if_pos (hcopM p hp hp2)] at e
        change coeff g (p ^ (r + 2)) = coeff g p * coeff g (p ^ (r + 1)) -
          1 * (p : ℂ) ^ ((2 : ℤ) - 1) * coeff g (p ^ r) at e
        rw [e, heckePrimePow' (by norm_num) squarefree_one p hp r, if_neg hp2', h1,
          ih (r + 1) (by omega), ih r (by omega)]
        norm_num
  refine ⟨fun n hn => ?_, fun n => ?_⟩
  · -- odd `n`
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow p k hp hk =>
      have hp2 : p ≠ 2 := by
        rintro rfl
        have : 2 ∣ 2 ^ k := dvd_pow_self 2 (by omega)
        omega
      exact hpp p hp hp2 k
    | zero => omega
    | one => rw [heckeCoeff_one]; exact g.isNorm
    | coprime a b _ _ hab ha hb =>
      obtain ⟨ha', hb'⟩ := Nat.odd_mul.mp (Nat.odd_iff.mpr hn)
      have hao : a % 2 = 1 := Nat.odd_iff.mp ha'
      have hbo : b % 2 = 1 := Nat.odd_iff.mp hb'
      have := hmul a b hab
      change coeff g (a * b) = coeff g a * coeff g b at this
      rw [this, ha hao, hb hbo, heckeMult 1 a b hab]
  · -- `a_{2n} = a₂ a_n`
    have hχ2 : (MulChar.ofUnitHom g.χ : DirichletCharacter ℂ M) ((2 : ℕ) : ZMod M) = 0 := by
      have h := hχp 2
      rw [if_neg] at h
      · exact h
      · rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
        exact not_not.mpr hM2
    have h2pow : ∀ j : ℕ, coeff g (2 ^ j) = coeff g 2 ^ j := by
      intro j
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        match j, ih with
        | 0, _ => simp only [pow_zero]; exact g.isNorm
        | 1, _ => simp
        | r + 2, ih =>
          have e := hpow 2 Nat.prime_two r
          rw [hχ2, zero_mul, zero_mul, sub_zero] at e
          change coeff g (2 ^ (r + 2)) = coeff g 2 * coeff g (2 ^ (r + 1)) at e
          rw [e, ih (r + 1) (by omega), pow_succ' (coeff g 2) (r + 1)]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [mul_zero]
      have h0 : coeff g 0 = 0 := CuspFormClass.qExpansion_coeff_zero _ one_pos
        (TauCeti.one_mem_strictPeriods_Gamma1_map M)
      rw [h0, mul_zero]
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hn.ne'
    have hcop : ∀ j, Nat.Coprime (2 ^ j) m := fun j =>
      Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)
    have e1 := hmul (2 ^ (k + 1)) m (hcop (k + 1))
    have e2 := hmul (2 ^ k) m (hcop k)
    change coeff g (2 ^ (k + 1) * m) = coeff g (2 ^ (k + 1)) * coeff g m at e1
    change coeff g (2 ^ k * m) = coeff g (2 ^ k) * coeff g m at e2
    rw [show 2 * (2 ^ k * m) = 2 ^ (k + 1) * m by ring, e1, e2, h2pow, h2pow, pow_succ']
    ring


/-! ### `f₁ = g − a₂ V₂ g` -/

theorem qParam_two_mul (τ : ℂ) :
    Function.Periodic.qParam 1 (2 * τ) = Function.Periodic.qParam 1 τ ^ 2 := by
  simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1; push_cast; ring

theorem two_mul_im_pos (τ : ℍ) : 0 < (2 * (τ : ℂ)).im := by simp; exact τ.im_pos

/-- **`f₁(τ) = g(τ) − a₂(g) g(2τ)`** under the coefficient facts. -/
theorem F₁_eq_sub {M : ℕ} [NeZero M] (g : Newform M 2)
    (hodd : ∀ n : ℕ, n % 2 = 1 → coeff g n = heckeCoeff 1 n)
    (heven : ∀ n : ℕ, coeff g (2 * n) = coeff g 2 * coeff g n) (τ : ℍ) :
    F₁ τ = g.toCuspForm τ - coeff g 2 * g.toCuspForm ⟨2 * (τ : ℂ), two_mul_im_pos τ⟩ := by
  set q := Function.Periodic.qParam 1 (τ : ℂ) with hq
  set a : ℕ → ℂ := fun n => coeff g n with ha
  have hΓ := TauCeti.one_mem_strictPeriods_Gamma1_map M
  have hg : HasSum (fun n => a n * q ^ n) (g.toCuspForm τ) :=
    ModularForm.hasSum_qExpansion g.toCuspForm one_pos hΓ τ
  have hg2 : HasSum (fun n => a n * (q ^ 2) ^ n)
      (g.toCuspForm ⟨2 * (τ : ℂ), two_mul_im_pos τ⟩) := by
    have := ModularForm.hasSum_qExpansion g.toCuspForm one_pos hΓ ⟨2 * (τ : ℂ), two_mul_im_pos τ⟩
    simpa [qParam_two_mul, ha, hq, coeff] using this
  have hF : HasSum (fun n => heckeCoeff 1 n * q ^ n) (F₁ τ) := by
    have := etaThetaIdentity τ
    have hq' : q = cexp (2 * π * I * τ) := by simp [hq, Function.Periodic.qParam]
    rw [hq']; exact this
  -- split the `g`-series
  have hs := hg.summable
  have hse : HasSum (fun m => a (2 * m) * q ^ (2 * m)) (coeff g 2 * g.toCuspForm
      ⟨2 * (τ : ℂ), two_mul_im_pos τ⟩) := by
    refine (hg2.mul_left (coeff g 2)).congr_fun fun m => ?_
    simp only [ha, heven, pow_mul]
    ring
  have hso : HasSum (fun m => a (2 * m + 1) * q ^ (2 * m + 1))
      (g.toCuspForm τ - coeff g 2 * g.toCuspForm ⟨2 * (τ : ℂ), two_mul_im_pos τ⟩) := by
    have hsum_o : Summable (fun m => a (2 * m + 1) * q ^ (2 * m + 1)) :=
      hs.comp_injective (i := fun m : ℕ => 2 * m + 1) (fun x y h => by simpa using h)
    have := HasSum.even_add_odd (f := fun n => a n * q ^ n) hse hsum_o.hasSum
    have hu := this.unique hg
    rw [← hu]; simp only [add_sub_cancel_left]; exact hsum_o.hasSum
  -- split the `f₁`-series
  have hFs := hF.summable
  have hFe : HasSum (fun m => heckeCoeff 1 (2 * m) * q ^ (2 * m)) 0 := by
    simp only [heckeCoeff_one_even, zero_mul]; exact hasSum_zero
  have hFo : HasSum (fun m => heckeCoeff 1 (2 * m + 1) * q ^ (2 * m + 1))
      (g.toCuspForm τ - coeff g 2 * g.toCuspForm ⟨2 * (τ : ℂ), two_mul_im_pos τ⟩) := by
    refine hso.congr_fun fun m => ?_
    simp only [ha]
    rw [hodd (2 * m + 1) (by omega)]
  have := HasSum.even_add_odd (f := fun n => heckeCoeff 1 n * q ^ n) hFe hFo
  rw [zero_add] at this
  exact hF.unique this


/-! ### Behaviour at `i∞` -/

theorem F₁_eq_prod (τ : ℂ) :
    F₁ τ = cexp (2 * π * I * τ) *
      (gp (cexp (2 * π * I * τ)) (-1) 4 4 ^ 2 * gp (cexp (2 * π * I * τ)) (-1) 8 8 ^ 2) := by
  have e4 : ∏' n : ℕ, (1 - eta_q n (4 * τ)) = gp (cexp (2 * π * I * τ)) (-1) 4 4 := by
    have := eta_tprod_eq_gp τ 4; push_cast at this; exact this
  have e8 : ∏' n : ℕ, (1 - eta_q n (8 * τ)) = gp (cexp (2 * π * I * τ)) (-1) 8 8 := by
    have := eta_tprod_eq_gp τ 8; push_cast at this; exact this
  have hq24 : Function.Periodic.qParam 24 (4 * τ) ^ 2 *
      Function.Periodic.qParam 24 (8 * τ) ^ 2 = cexp (2 * π * I * τ) := by
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold F₁
  rw [ModularForm.eta, ModularForm.eta, e4, e8, ← hq24]
  ring

theorem qParam_one_eq (τ : ℂ) : Function.Periodic.qParam 1 τ = cexp (2 * π * I * τ) := by
  simp [Function.Periodic.qParam]

theorem tendsto_F₁_div_q :
    Tendsto (fun τ : ℍ => F₁ τ / Function.Periodic.qParam 1 (τ : ℂ)) atImInfty (𝓝 1) := by
  have hq := UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) one_pos
  have h4 := (tendsto_gp_nhds_zero (-1) 4 4 (by norm_num) (by norm_num)).comp hq
  have h8 := (tendsto_gp_nhds_zero (-1) 8 8 (by norm_num) (by norm_num)).comp hq
  have := (h4.pow 2).mul (h8.pow 2)
  rw [one_pow, one_mul] at this
  refine this.congr fun τ => ?_
  simp only [Function.comp_apply]
  rw [F₁_eq_prod, ← qParam_one_eq, mul_div_cancel_left₀ _
    (Function.Periodic.qParam_ne_zero (τ : ℂ))]

theorem mul_im_pos_of_nat {j : ℕ} (hj : 0 < j) (τ : ℍ) : 0 < ((j : ℂ) * τ).im := by
  simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero]
  exact mul_pos (by exact_mod_cast hj) τ.im_pos

/-- A cusp form at `jτ`, `j ≥ 2`, is `o(q)` at `i∞`. -/
theorem tendsto_cusp_mul_div_q {M : ℕ} [NeZero M] (G : CuspForm ((Gamma1 M).map (mapGL ℝ)) 2)
    {j : ℕ} (hj : 2 ≤ j) :
    Tendsto (fun τ : ℍ => G ⟨(j : ℂ) * τ, mul_im_pos_of_nat (by omega) τ⟩ /
      Function.Periodic.qParam 1 (τ : ℂ)) atImInfty (𝓝 0) := by
  have hO := CuspFormClass.exp_decay_atImInfty G one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map M)
  have hw : Tendsto (fun τ : ℍ => (⟨(j : ℂ) * τ, mul_im_pos_of_nat (by omega) τ⟩ : ℍ))
      atImInfty atImInfty := by
    refine tendsto_affine_atImInfty (α := j) (δ := 1) (by exact_mod_cast (by omega : 0 < j))
      one_pos 0 _ (fun τ => ?_)
    simp
  obtain ⟨C, hC⟩ := (hO.comp_tendsto hw).bound
  have hq := UpperHalfPlane.qParam_tendsto_atImInfty (h := 1) one_pos
  have hqn : Tendsto (fun τ : ℍ => C * ‖Function.Periodic.qParam 1 (τ : ℂ)‖) atImInfty (𝓝 0) := by
    have := (hq.norm).const_mul C
    simpa using this
  refine squeeze_zero_norm' ?_ hqn
  filter_upwards [hC] with τ hτ
  simp only [Function.comp_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hτ
  rw [norm_div, Function.Periodic.norm_qParam]
  have hjτ : (⟨(j : ℂ) * τ, mul_im_pos_of_nat (by omega) τ⟩ : ℍ).im = j * τ.im := by
    change ((j : ℂ) * (τ : ℂ)).im = j * τ.im
    simp only [mul_im, natCast_re, natCast_im, zero_mul, add_zero, UpperHalfPlane.coe_im]
  rw [hjτ] at hτ
  have him : 0 < τ.im := τ.im_pos
  have hpos : 0 < Real.exp (-2 * π * (τ : ℂ).im / 1) := Real.exp_pos _
  rw [div_le_iff₀ hpos]
  have hjr : (2 : ℝ) ≤ j := by exact_mod_cast hj
  have hC0 : 0 ≤ C := by
    by_contra hneg
    rw [not_le] at hneg
    have := norm_nonneg (G ⟨(j : ℂ) * τ, mul_im_pos_of_nat (by omega) τ⟩)
    have : C * Real.exp (-2 * π * (j * τ.im) / 1) < 0 := mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
    linarith
  calc ‖G ⟨(j : ℂ) * τ, mul_im_pos_of_nat (by omega) τ⟩‖
      ≤ C * Real.exp (-2 * π * (j * τ.im) / 1) := hτ
    _ ≤ C * Real.exp (-2 * π * (τ : ℂ).im / 1) * Real.exp (-2 * π * (τ : ℂ).im / 1) := by
      rw [mul_assoc C, ← Real.exp_add]
      apply mul_le_mul_of_nonneg_left _ hC0
      apply Real.exp_le_exp.mpr
      simp only [UpperHalfPlane.coe_im, div_one]
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ j - 2) him.le) Real.pi_pos.le]


/-! ### No newform of level dividing 16 -/

theorem fricke32_im_pos (τ : ℍ) : 0 < (-1 / (32 * (τ : ℂ))).im := by
  have := UpperHalfPlane.im_inv_neg_coe_pos
    (⟨32 * (τ : ℂ), by simp; exact τ.im_pos⟩ : ℍ)
  simpa [neg_div, inv_neg, one_div] using this

theorem dirichletLift_eq_one {M : ℕ} [NeZero M] (g : Newform M 2) (hχ : g.χ = 1) :
    g.dirichletLift = 1 := by
  rw [Newform.dirichletLift_def, hχ]
  ext u
  simp

/-- **There is no newform of level `M ∣ 16`, `2 ∣ M`, trivial character, with the eigenvalues
of `f₁` at the odd primes.** -/
theorem false_of_newform_dvd_16 {M : ℕ} [NeZero M] (hM16 : M ∣ 16) (hM2 : 2 ∣ M)
    (g : Newform M 2) (hχ : g.χ = 1)
    (hgood : ∀ p : ℕ, p.Prime → p ≠ 2 → coeff g p = heckeCoeff 1 p) : False := by
  obtain ⟨hodd, heven⟩ := coeff_newform_odd_even hM16 hM2 g hχ hgood
  obtain ⟨c, hc⟩ := newform_fricke g hχ
  obtain ⟨j, hj⟩ : ∃ j, M * j = 32 := ⟨32 / M, Nat.mul_div_cancel' (hM16.trans ⟨2, rfl⟩)⟩
  obtain ⟨j', hj'⟩ : ∃ j', M * j' = 16 := ⟨16 / M, Nat.mul_div_cancel' hM16⟩
  have hMle : M ≤ 16 := Nat.le_of_dvd (by norm_num) hM16
  have hj2 : 2 ≤ j := by
    by_contra h
    have : j ≤ 1 := by omega
    have : M * j ≤ 16 * 1 := Nat.mul_le_mul hMle this
    omega
  have hj'1 : 0 < j' := Nat.pos_of_ne_zero (by rintro rfl; simp at hj')
  have ha2 : j' = 1 → coeff g 2 = 0 := by
    intro h1
    subst h1
    have hM : M = 16 := by simpa using hj'
    subst hM
    exact Newform.qExpansion_coeff_prime_eq_zero_of_sq_dvd g Nat.prime_two (by norm_num)
      ⟨by norm_num, 1, by rw [dirichletLift_eq_one g hχ, DirichletCharacter.changeLevel_one]⟩
  have hMj : (M : ℂ) * j = 32 := by exact_mod_cast hj
  have hMj' : (M : ℂ) * j' = 16 := by exact_mod_cast hj'
  -- the key identity
  have key : ∀ τ : ℍ, -32 * F₁ τ = c * (j : ℂ) ^ 2 *
      g.toCuspForm ⟨(j : ℂ) * τ, mul_im_pos_of_nat (by omega) τ⟩ -
        coeff g 2 * c * (j' : ℂ) ^ 2 * g.toCuspForm ⟨(j' : ℂ) * τ, mul_im_pos_of_nat hj'1 τ⟩ := by
    intro τ
    have hτ0 : (τ : ℂ) ≠ 0 := τ.ne_zero
    set w : ℍ := ⟨-1 / (32 * (τ : ℂ)), fricke32_im_pos τ⟩ with hw
    have e1 := F₁_eq_sub g hodd heven w
    have e2 : F₁ w = -32 * (τ : ℂ) ^ 2 * F₁ τ := F₁_fricke τ.im_pos
    have hpt1 : (-1 / ((M : ℂ) * ((j : ℂ) * τ))) = -1 / (32 * (τ : ℂ)) := by
      rw [← mul_assoc, hMj]
    have hpt2 : (-1 / ((M : ℂ) * ((j' : ℂ) * τ))) = 2 * (-1 / (32 * (τ : ℂ))) := by
      rw [← mul_assoc, hMj']; field_simp; ring
    have e3 := hc ((j : ℂ) * τ) (mul_im_pos_of_nat (by omega) τ) (by rw [hpt1]; exact w.2)
    have e4 := hc ((j' : ℂ) * τ) (mul_im_pos_of_nat hj'1 τ) (by rw [hpt2]; exact two_mul_im_pos w)
    have hw1 : g.toCuspForm w = g.toCuspForm ⟨-1 / ((M : ℂ) * ((j : ℂ) * τ)),
        by rw [hpt1]; exact w.2⟩ :=
      congrArg g.toCuspForm (UpperHalfPlane.ext (by simp [hw, hpt1]))
    have hw2 : g.toCuspForm ⟨2 * (w : ℂ), two_mul_im_pos w⟩ =
        g.toCuspForm ⟨-1 / ((M : ℂ) * ((j' : ℂ) * τ)), by rw [hpt2]; exact two_mul_im_pos w⟩ :=
      congrArg g.toCuspForm (UpperHalfPlane.ext (by simp [hw, hpt2]))
    rw [e2, hw1, hw2, e3, e4] at e1
    have hτ2 : (τ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hτ0
    apply mul_left_cancel₀ hτ2
    linear_combination e1
  -- divide by `q` and let `Im τ → ∞`
  have hL : Tendsto (fun τ : ℍ => -32 * (F₁ τ / Function.Periodic.qParam 1 (τ : ℂ))) atImInfty
      (𝓝 (-32 * 1)) := tendsto_F₁_div_q.const_mul _
  have hR : Tendsto (fun τ : ℍ => -32 * (F₁ τ / Function.Periodic.qParam 1 (τ : ℂ))) atImInfty
      (𝓝 0) := by
    have hA := (tendsto_cusp_mul_div_q g.toCuspForm hj2).const_mul (c * (j : ℂ) ^ 2)
    have hB : Tendsto (fun τ : ℍ => coeff g 2 * c * (j' : ℂ) ^ 2 *
        (g.toCuspForm ⟨(j' : ℂ) * τ, mul_im_pos_of_nat hj'1 τ⟩ /
          Function.Periodic.qParam 1 (τ : ℂ))) atImInfty (𝓝 0) := by
      by_cases h1 : j' = 1
      · rw [ha2 h1]; simp
      · have := (tendsto_cusp_mul_div_q g.toCuspForm (j := j') (by omega)).const_mul
          (coeff g 2 * c * (j' : ℂ) ^ 2)
        simpa using this
    have := hA.sub hB
    rw [mul_zero, sub_zero] at this
    refine this.congr fun τ => ?_
    rw [show -32 * (F₁ τ / Function.Periodic.qParam 1 (τ : ℂ)) =
      (-32 * F₁ τ) / Function.Periodic.qParam 1 (τ : ℂ) by ring, key τ]
    ring
  have := tendsto_nhds_unique hL hR
  norm_num at this


/-! ### `f₁` is new at level 32 -/

theorem false_of_newform_level_one (g : Newform 1 2) : False := by
  have h : 𝒮ℒ ≤ (Gamma1 1).map (mapGL ℝ) := le_of_eq TauCeti.Gamma1_one_map_eq_SL.symm
  set G : CuspForm 𝒮ℒ 2 := CuspForm.restrict h g.toCuspForm
  have hG : G = 0 :=
    rank_zero_iff_forall_zero.mp (CuspForm.rank_eq_zero_of_weight_lt_twelve (by norm_num)) G
  apply g.ne_zero
  ext τ
  have := congrArg (fun F : CuspForm 𝒮ℒ 2 => (⇑F) τ) hG
  simpa [G] using this

/-- **`η(4τ)² η(8τ)²` is new at level 32** (the conductor of `y² = x³ − x` is 32). -/
theorem newAt32 : NewAt32 := by
  intro F hF
  have hc : ∀ n, (qExpansion 1 (restrict32 etaForm32)).coeff n = heckeCoeff 1 n := fun n => by
    rw [qExpansion_restrict32, qExpansion_etaForm32_coeff]
  have hFeq : F = restrict32 etaForm32 := by
    apply CuspForm.qExpansion_injective one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map 32)
    ext n
    show (qExpansion 1 F).coeff n = (qExpansion 1 (restrict32 etaForm32)).coeff n
    rw [hF, hc]
  rw [hFeq]
  obtain ⟨E, hE, hEχ⟩ := exists_eigenformAway32
  obtain ⟨M, hM0, hMN, g, hgχ, hgev⟩ :=
    Newform.exists_newform_comp_unitsMap_eq_and_eigenvalue_eq_of_forall_heckeTCuspNat_eq_smul
      E.mem_charSpace E.ne_zero (a := fun p hp hpN => E.eigenvalue ⟨p, hp.pos⟩ hpN)
      (fun p hp hpN => E.heckeTCuspNat_eq_eigenvalue_smul hp hpN)
  have hg1 : g.χ = 1 := by
    rw [hEχ] at hgχ
    ext u
    obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hMN u
    have := congrArg (fun φ => ((φ v : ℂˣ) : ℂ)) hgχ
    simpa using this
  have hE1 : (qExpansion 1 E.toCuspForm).coeff 1 = 1 := by rw [hE, hc 1, heckeCoeff_one]
  have hgood : ∀ p : ℕ, p.Prime → p ≠ 2 → coeff g p = heckeCoeff 1 p := by
    intro p hp hp2
    have hpN : Nat.Coprime p 32 := by
      have : Nat.Coprime p (2 ^ 5) := Nat.Coprime.pow_right 5
        ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
      simpa using this
    have e1 := g.qExpansion_coeff_eq_eigenvalue g.isNorm ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hMN)
    have e2 := E.qExpansion_coeff_eq_eigenvalue hE1 ⟨p, hp.pos⟩ hpN
    rw [hE, hc] at e2
    change coeff g p = _ at e1
    rw [e1, hgev p hp hpN]
    exact e2.symm
  have hMd : M ∈ Nat.divisors 32 := Nat.mem_divisors.mpr ⟨hMN, by norm_num⟩
  have hdiv : Nat.divisors 32 = {1, 2, 4, 8, 16, 32} := by decide
  rw [hdiv] at hMd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hMd
  rcases hMd with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (false_of_newform_level_one g).elim
  · exact (false_of_newform_dvd_16 (by norm_num) (by norm_num) g hg1 hgood).elim
  · exact (false_of_newform_dvd_16 (by norm_num) (by norm_num) g hg1 hgood).elim
  · exact (false_of_newform_dvd_16 (by norm_num) (by norm_num) g hg1 hgood).elim
  · exact (false_of_newform_dvd_16 (by norm_num) (by norm_num) g hg1 hgood).elim
  · -- level 32: `f₁ = g`
    have hmem : restrict32 etaForm32 ∈ cuspFormCharSpace 2 g.χ := by
      rw [hg1, ← hEχ, ← hE]; exact E.mem_charSpace
    have hfg := g.eq_qExpansion_coeff_one_smul_of_forall_prime_heckeTCuspNat_eq_smul hmem
      (fun p hp hpN => by
        have := E.heckeTCuspNat_eq_eigenvalue_smul hp hpN
        rw [hE] at this
        rw [this, ← hgev p hp hpN])
    rw [hfg, hc 1, heckeCoeff_one, one_smul]
    exact g.isNew

/-- **The leaf from Atkin–Li alone.** -/
theorem heckeThetaNewform_of_atkinLi (hAL : AtkinLiTwistNew) : ZInQ.GZDecomp.HeckeThetaNewform :=
  heckeThetaNewform_of_newAt32_atkinLi newAt32 hAL

/-- **The headline with gz-decomp's leaves, L1 reduced to Atkin–Li.** -/
theorem frozenTarget_of_sixContactMin_tyzThm35ReadingA_atkinLi_gzLeaves (hH : ZInQ.SixContactMin)
    (hA : ZInQ.Literature.TYZThm35ReadingA) (hAL : AtkinLiTwistNew)
    (hL2 : ZInQ.GZDecomp.FHNonvanishing) (hL3 : ZInQ.GZDecomp.GrossZagierHeegner) :
    ZInQ.FrozenTarget :=
  ZInQ.GZDecomp.frozenTarget_of_sixContactMin_tyzThm35ReadingA_gzLeaves hH hA
    (heckeThetaNewform_of_atkinLi hAL) hL2 hL3

end ZInQ.GZTheta
