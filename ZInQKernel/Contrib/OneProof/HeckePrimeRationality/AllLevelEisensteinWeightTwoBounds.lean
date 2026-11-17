import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelEisensteinWeightTwo

/-!
# Cusp bounds for the actual weight-two division Eisenstein series

The one-dimensional inverse-square row formula supplies geometric bounds
uniform at large imaginary height. No weight-three summability theorem is
applied to an unregularized weight-two lattice sum.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open Complex Filter Matrix ModularForm CongruenceSubgroup
open scoped Topology Real UpperHalfPlane Modular MatrixGroups Manifold

namespace ZInQ.Contrib.HeckePrimeRationality.EisensteinWeightTwo

open ZInQ.Contrib.HeckePrimeRationality

def inverseSquareRow (w : ℂ) : ℂ := ∑' n : ℤ, 1 / (w + (n : ℂ)) ^ 2

lemma inverseSquareRow_neg (w : ℂ) : inverseSquareRow (-w) = inverseSquareRow w := by
  unfold inverseSquareRow
  rw [← (Equiv.neg ℤ).tsum_eq]
  refine tsum_congr fun n => ?_
  simp only [Equiv.neg_apply, Int.cast_neg]
  rw [show -w + -(n : ℂ) = -(w + (n : ℂ)) by ring, neg_sq]

lemma inverseSquareRow_q {w : ℂ} (hw : 0 < w.im) :
    inverseSquareRow w = (-4 * (Real.pi : ℂ) ^ 2) *
      (cexp (2 * (Real.pi : ℂ) * I * w) / (1 - cexp (2 * (Real.pi : ℂ) * I * w)) ^ 2) := by
  have h := EisensteinSeries.qExpansion_identity (k := 1) (by norm_num) (⟨w, hw⟩ : ℍ)
  have hq := UpperHalfPlane.norm_exp_two_pi_I_lt_one (⟨w, hw⟩ : ℍ)
  have hc : (-2 * (Real.pi : ℂ) * I) ^ 2 = -4 * (Real.pi : ℂ) ^ 2 := by
    norm_num [mul_pow, I_sq]
  simpa only [inverseSquareRow, Nat.reduceAdd, Nat.factorial_one, Nat.cast_one,
    div_one, pow_one, hc, (hasSum_coe_mul_geometric_of_norm_lt_one hq).tsum_eq] using h

lemma norm_row_q {w : ℂ} (hw : 0 < w.im) :
    ‖inverseSquareRow w‖ = 4 * Real.pi ^ 2 * Real.exp (-2 * Real.pi * w.im) /
      ‖1 - cexp (2 * (Real.pi : ℂ) * I * w)‖ ^ 2 := by
  rw [inverseSquareRow_q hw, norm_mul, norm_div, norm_pow, Complex.norm_exp]
  have he : (2 * (Real.pi : ℂ) * I * w).re = -2 * Real.pi * w.im := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [he]
  simp [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    mul_div_assoc]

lemma inverseSquareRow_norm_le_pos {w : ℂ} (hw : 0 < w.im) {r : ℝ}
    (hr : r < 1) (hqr : Real.exp (-2 * Real.pi * w.im) ≤ r) :
    ‖inverseSquareRow w‖ ≤ (4 * Real.pi ^ 2 / (1 - r) ^ 2) * Real.exp (-2 * Real.pi * w.im) := by
  have h1r : 0 < 1 - r := by linarith
  have hqnorm : ‖cexp (2 * (Real.pi : ℂ) * I * w)‖ = Real.exp (-2 * Real.pi * w.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp [Complex.mul_re, Complex.mul_im]
  have hden : 1 - r ≤ ‖1 - cexp (2 * (Real.pi : ℂ) * I * w)‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (cexp (2 * (Real.pi : ℂ) * I * w))
    rw [norm_one, hqnorm] at h
    linarith
  rw [norm_row_q hw]
  calc _ ≤ 4 * Real.pi ^ 2 * Real.exp (-2 * Real.pi * w.im) / (1 - r) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [norm_nonneg (1 - cexp (2 * (Real.pi : ℂ) * I * w))])
    _ = _ := by ring

lemma inverseSquareRow_norm_le {w : ℂ} (hw : w.im ≠ 0) {r : ℝ}
    (hr : r < 1) (hqr : Real.exp (-2 * Real.pi * |w.im|) ≤ r) :
    ‖inverseSquareRow w‖ ≤ (4 * Real.pi ^ 2 / (1 - r) ^ 2) * Real.exp (-2 * Real.pi * |w.im|) := by
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · have h := inverseSquareRow_norm_le_pos (w := -w) (by simp; linarith) hr
      (by simpa [abs_of_neg hneg] using hqr)
    simpa [inverseSquareRow_neg, abs_of_neg hneg] using h
  · simpa only [abs_of_pos hpos] using inverseSquareRow_norm_le_pos hpos hr
      (by simpa only [abs_of_pos hpos] using hqr)

lemma torsionPoint_im (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    (CompletedTheta.torsionPoint N a b τ).im = (a : ℝ) * τ.im / N := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have h : (N : ℂ) * CompletedTheta.torsionPoint N a b τ = (a : ℂ) * (τ : ℂ) + (b : ℂ) := by
    unfold CompletedTheta.torsionPoint
    field_simp
  have hi := congrArg Complex.im h
  simp at hi
  apply (eq_div_iff hNr).mpr
  linear_combination hi

lemma abs_int_shift_bound (N : ℕ) (hN : 0 < N) (a m : ℤ)
    (ha0 : 0 ≤ a) (haN : a < N) (hm : m ≠ 0) : |m| ≤ |a + (N : ℤ) * m| := by
  have hNz : (1 : ℤ) ≤ N := by exact_mod_cast hN
  rcases le_or_gt 0 m with hpos | hneg
  · rw [abs_of_nonneg hpos, abs_of_nonneg (by positivity)]
    nlinarith
  · have hm1 : m ≤ -1 := by omega
    have ha1 : a ≤ (N : ℤ) - 1 := by omega
    have hsum : a + (N : ℤ) * m < 0 := by nlinarith
    rw [abs_of_neg hneg, abs_of_neg hsum]
    nlinarith

lemma abs_shift_im_lower (N : ℕ) (hN : 0 < N) (a b m : ℤ) (τ : ℍ)
    (ha0 : 0 ≤ a) (haN : a < N) (hm : m ≠ 0) (hy : 1 ≤ τ.im) :
    (m.natAbs : ℝ) / N ≤ |(CompletedTheta.torsionPoint N a b τ + (m : ℂ) * (τ : ℂ)).im| := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hi : (m.natAbs : ℝ) ≤ |(a : ℝ) + (N : ℝ) * (m : ℝ)| := by
    rw [Nat.cast_natAbs]
    exact_mod_cast abs_int_shift_bound N hN a m ha0 haN hm
  have heq : (N : ℝ) * |(a : ℝ) / N + (m : ℝ)| = |(a : ℝ) + (N : ℝ) * (m : ℝ)| := by
    have he := abs_mul (N : ℝ) ((a : ℝ) / N + (m : ℝ))
    rw [abs_of_pos hNr] at he
    rw [← he]
    congr 1
    field_simp [hNr.ne']
  have hcoef : (m.natAbs : ℝ) / N ≤ |(a : ℝ) / N + (m : ℝ)| := by
    rw [div_le_iff₀ hNr, mul_comm]
    rwa [heq]
  have him : (CompletedTheta.torsionPoint N a b τ + (m : ℂ) * (τ : ℂ)).im =
      ((a : ℝ) / N + (m : ℝ)) * τ.im := by
    simp [torsionPoint_im N hN a b τ]
    ring
  rw [him, abs_mul, abs_of_pos τ.im_pos]
  exact hcoef.trans (le_mul_of_one_le_right (abs_nonneg _) hy)

/-- An explicit height-uniform bound for the genuine iterated inverse-square rows. -/
theorem shifted_rows_bounded (N : ℕ) (hN : 0 < N) (a b : ℤ)
    (ha0 : 0 ≤ a) (haN : a < N) :
    ∃ M : ℝ, ∀ τ : ℍ, 1 ≤ τ.im →
      ‖∑' m : ℤ, ∑' n : ℤ, 1 / (CompletedTheta.torsionPoint N a b τ +
        (m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2‖ ≤ M := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  let r : ℝ := Real.exp (-2 * Real.pi / N)
  let C : ℝ := 4 * Real.pi ^ 2 / (1 - r) ^ 2
  let K : ℝ := ‖inverseSquareRow ((b : ℂ) / N)‖
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by
    change Real.exp (-2 * Real.pi / N) < 1
    rw [Real.exp_lt_one_iff]
    exact div_neg_of_neg_of_pos (by nlinarith [Real.pi_pos]) hNr
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hg := ThetaFive.hasSum_geom_natAbs C hr0 hr1
  have hd : Summable (fun m : ℤ => if m = 0 then K else 0) :=
    summable_of_hasFiniteSupport ((Set.finite_singleton (0 : ℤ)).subset (by simp))
  let Mterm : ℤ → ℝ := fun m => C * r ^ m.natAbs + if m = 0 then K else 0
  have hM : Summable Mterm := hg.summable.add hd
  refine ⟨C / (1 - r) + C * r / (1 - r) + K, fun τ hy => ?_⟩
  have hbound (m : ℤ) :
      ‖inverseSquareRow (CompletedTheta.torsionPoint N a b τ + (m : ℂ) * (τ : ℂ))‖ ≤ Mterm m := by
    by_cases hm : m = 0
    · subst m
      simp only [Mterm, Int.natAbs_zero, pow_zero, mul_one]
      by_cases ha : a = 0
      · simp [ha, CompletedTheta.torsionPoint, K]
        linarith
      · have ha1 : (1 : ℤ) ≤ a := by omega
        have hi : 1 / (N : ℝ) ≤ |(CompletedTheta.torsionPoint N a b τ).im| := by
          rw [torsionPoint_im N hN a b τ, abs_div, abs_mul, abs_of_pos τ.im_pos, abs_of_pos hNr,
            abs_of_nonneg (by exact_mod_cast ha0)]
          have har : (1 : ℝ) ≤ a := by exact_mod_cast ha1
          have hp : (1 : ℝ) ≤ (a : ℝ) * τ.im := by
            nlinarith [mul_nonneg (sub_nonneg.mpr har) (sub_nonneg.mpr hy)]
          exact div_le_div_of_nonneg_right hp hNr.le
        have hq : Real.exp (-2 * Real.pi * |(CompletedTheta.torsionPoint N a b τ).im|) ≤ r := by
          change Real.exp (-2 * Real.pi * |(CompletedTheta.torsionPoint N a b τ).im|) ≤
            Real.exp (-2 * Real.pi / N)
          apply Real.exp_le_exp.mpr
          calc _ ≤ (-2 * Real.pi) * (1 / (N : ℝ)) :=
              mul_le_mul_of_nonpos_left hi (by nlinarith [Real.pi_pos])
            _ = -2 * Real.pi / N := by ring
        have hw : (CompletedTheta.torsionPoint N a b τ).im ≠ 0 := by
          intro he; rw [he, abs_zero] at hi; have := one_div_pos.mpr hNr; linarith
        have h := inverseSquareRow_norm_le hw hr1 hq
        have he1 : Real.exp (-2 * Real.pi * |(CompletedTheta.torsionPoint N a b τ).im|) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos, abs_nonneg (CompletedTheta.torsionPoint N a b τ).im])
        have hK : 0 ≤ K := norm_nonneg _
        simpa only [Int.cast_zero, zero_mul, add_zero] using
          h.trans ((mul_le_mul_of_nonneg_left he1 hC).trans (by dsimp [C]; linarith))
    · have hi := abs_shift_im_lower N hN a b m τ ha0 haN hm hy
      have hm1 : (1 : ℝ) ≤ m.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hm
      have hi1 : 1 / (N : ℝ) ≤ |(CompletedTheta.torsionPoint N a b τ + (m : ℂ) * (τ : ℂ)).im| :=
        (div_le_div_of_nonneg_right hm1 hNr.le).trans hi
      have hw : (CompletedTheta.torsionPoint N a b τ + (m : ℂ) * (τ : ℂ)).im ≠ 0 := by
        intro he; rw [he, abs_zero] at hi1; have := one_div_pos.mpr hNr; linarith
      have hq : Real.exp (-2 * Real.pi * |(CompletedTheta.torsionPoint N a b τ +
          (m : ℂ) * (τ : ℂ)).im|) ≤ r := by
        change Real.exp (-2 * Real.pi * |(CompletedTheta.torsionPoint N a b τ +
          (m : ℂ) * (τ : ℂ)).im|) ≤ Real.exp (-2 * Real.pi / N)
        apply Real.exp_le_exp.mpr
        calc _ ≤ (-2 * Real.pi) * (1 / (N : ℝ)) :=
            mul_le_mul_of_nonpos_left hi1 (by nlinarith [Real.pi_pos])
          _ = -2 * Real.pi / N := by ring
      have hpow : Real.exp (-2 * Real.pi * |(CompletedTheta.torsionPoint N a b τ +
          (m : ℂ) * (τ : ℂ)).im|) ≤ r ^ m.natAbs := by
        change Real.exp (-2 * Real.pi * |(CompletedTheta.torsionPoint N a b τ +
          (m : ℂ) * (τ : ℂ)).im|) ≤ Real.exp (-2 * Real.pi / N) ^ m.natAbs
        rw [← Real.exp_nat_mul]
        apply Real.exp_le_exp.mpr
        calc _ ≤ (-2 * Real.pi) * ((m.natAbs : ℝ) / N) :=
            mul_le_mul_of_nonpos_left hi (by nlinarith [Real.pi_pos])
          _ = (m.natAbs : ℝ) * (-2 * Real.pi / N) := by ring
      have h := inverseSquareRow_norm_le hw hr1 hq
      simpa only [Mterm, ite_eq_right hm, add_zero] using h.trans (mul_le_mul_of_nonneg_left hpow hC)
  have hn : Summable (fun m : ℤ => ‖inverseSquareRow
      (CompletedTheta.torsionPoint N a b τ + (m : ℂ) * (τ : ℂ))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound hM
  have hb := (norm_tsum_le_tsum_norm hn).trans (hn.tsum_mono hM hbound)
  have he : (∑' m : ℤ, Mterm m) = C / (1 - r) + C * r / (1 - r) + K := by
    rw [hg.summable.tsum_add hd, hg.tsum_eq]
    simp
  rw [he] at hb
  simpa only [inverseSquareRow, add_assoc] using hb

/-- The actual weight-two lattice-series family is bounded at the cusp at infinity. -/
theorem divisionEisenstein_bounded (N : ℕ) (hN : 0 < N) (a b : ℤ) :
    UpperHalfPlane.IsBoundedAtImInfty (fun τ : ℍ => divisionEisenstein N a b τ) := by
  have hNz : (0 : ℤ) < N := by exact_mod_cast hN
  let a0 : ℤ := a % (N : ℤ)
  have ha0 : 0 ≤ a0 := Int.emod_nonneg a hNz.ne'
  have haN : a0 < N := Int.emod_lt_of_pos a hNz
  obtain ⟨M, hM⟩ := shifted_rows_bounded N hN a0 b ha0 haN
  have hE := EisensteinSeries.isBoundedAtImInfty_E2
  rw [UpperHalfPlane.isBoundedAtImInfty_iff] at hE ⊢
  obtain ⟨ME, AE, hE⟩ := hE
  refine ⟨M + ‖2 * riemannZeta 2‖ * ME, max 1 AE, fun τ hτ => ?_⟩
  have hy : 1 ≤ τ.im := (le_max_left _ _).trans hτ
  have hAE : AE ≤ τ.im := (le_max_right _ _).trans hτ
  have ha : a0 + (N : ℤ) * (a / N) = a := by
    have h := Int.mul_ediv_add_emod a (N : ℤ)
    dsimp only [a0]
    omega
  have hl := divisionEisenstein_add_level N hN a0 b (a / N) 0 τ
  rw [ha, mul_zero, add_zero] at hl
  have hrows := (hasSum_shifted_rows τ (CompletedTheta.torsionPoint N a0 b τ)).tsum_eq
  have he : divisionEisenstein N a0 b τ =
      (∑' m : ℤ, ∑' n : ℤ, 1 / (CompletedTheta.torsionPoint N a0 b τ +
        (m : ℂ) * (τ : ℂ) + (n : ℂ)) ^ 2) - EisensteinSeries.G2 τ := by
    rw [divisionEisenstein_eq_weierstrassP N hN]
    linear_combination -hrows
  have hG : ‖EisensteinSeries.G2 τ‖ ≤ ‖2 * riemannZeta 2‖ * ME := by
    rw [ThetaG2.G2_eq_smul_E2]
    change ‖(2 * riemannZeta 2) * EisensteinSeries.E2 τ‖ ≤ _
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hE τ hAE) (norm_nonneg _)
  rw [hl, he]
  exact (norm_sub_le _ _).trans (add_le_add (hM τ hy) hG)

/-- A genuine weight-two modular form, constructed from the convergent principal-divisor lattice series. -/
def divisionEisensteinMF (N : ℕ) (hN : 0 < N) (a : Fin 2 → ℤ) :
    ModularForm (CongruenceSubgroup.Gamma N) 2 where
  toFun τ := divisionEisenstein N (a 0) (a 1) τ
  slash_action_eq' := (divisionEisensteinSIF N hN a).slash_action_eq'
  holo' := divisionEisenstein_mdiff N hN (a 0) (a 1)
  bdd_at_cusps' {c} hc := by
    letI : NeZero N := ⟨hN.ne'⟩
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    intro γ _
    rw [divisionEisenstein_slash N hN a γ]
    exact divisionEisenstein_bounded N hN ((a ᵥ* γ.1) 0) ((a ᵥ* γ.1) 1)

/-- The genuine series-defined modular form has the supplied actual x-value on every good label. -/
theorem divisionEisensteinMF_eq_xValue (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    divisionEisensteinMF N hN ![a, b] τ = TorsionWeierstrassData.xValue N a b τ := by
  change divisionEisenstein N a b τ = _
  exact (xValue_eq_divisionEisenstein N hN a b τ hg).symm

/-- The form's value is the literal principal-lift Eisenstein sum divided by its level. -/
theorem divisionEisensteinMF_eq_principalLift (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    divisionEisensteinMF N hN ![a, b] τ = (∑' p : ℤ × ℤ, principalLiftTerm N a b τ p) / (N : ℂ) := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  change divisionEisenstein N a b τ = _
  rw [divisionEisenstein_eq_weierstrassP N hN, (hasSum_principalLiftTerm N hN a b τ).tsum_eq]
  exact (mul_div_cancel_left₀ _ hNc).symm

/-- The all-label contract respects the stipulated zero value on every bad torsion class. -/
theorem divisionEisensteinMF_eq_xValue_all (N : ℕ) (hN : 0 < N) (a b : ℤ) (τ : ℍ) :
    divisionEisensteinMF N hN ![a, b] τ = TorsionWeierstrassData.xValue N a b τ := by
  by_cases hg : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · change divisionEisenstein N a b τ = TorsionWeierstrassData.xValue N a b τ
    rw [divisionEisenstein_zero_of_bad N hN a b hg, TorsionWeierstrassData.xValue, ite_eq_left hg]
  · exact divisionEisensteinMF_eq_xValue N hN a b τ hg

/-- Both moments of the explicit principal lift vanish. -/
theorem principalLift_moments (N : ℕ) (a b : ℤ) (τ : ℍ) :
    ((N + 1 : ℂ) - 1 - (N : ℂ) = 0) ∧
      ((N + 1 : ℂ) * CompletedTheta.torsionPoint N a b τ -
        (N + 1 : ℂ) * CompletedTheta.torsionPoint N a b τ - (N : ℂ) * 0 = 0) := by
  constructor <;> ring

end ZInQ.Contrib.HeckePrimeRationality.EisensteinWeightTwo
