import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionWeightThree
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCorrelation

/-!
# Finite weight-three Fourier identity from the actual theta-kernel germ

The third derivative is taken only after equality of ordinary analytic germs.
The zero Fourier row follows from oddness of actual torsion values and finite
reindexing. No weight-three value is defined as a Fourier transform.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open Complex Filter Function
open scoped Topology Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionWeightThree

open ZInQ.Contrib.HeckePrimeRationality
open CompletedTheta TorsionWeierstrassData TorsionMuFourierKernel
open TorsionFourierComparison

variable (N : ℕ) [NeZero N]

theorem kernelUnit_third_finite (a b : Fin N) (τ : ℍ) :
    iteratedDeriv 3 (kernelUnit N (a : ℕ) (b : ℕ) τ) 0 =
      (N : ℂ) ^ 2 * (cubicValue N (a : ℕ) (b : ℕ) τ + yValue N (a : ℕ) (b : ℕ) τ) := by
  by_cases hg : ¬ ((N : ℤ) ∣ ((a : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((b : ℕ) : ℤ))
  · exact kernelUnit_third_zero N (a : ℕ) (b : ℕ) τ hg
  · have hab : a = 0 ∧ b = 0 := by
      have h := (finite_good_iff N a b).not.mp hg
      tauto
    obtain ⟨rfl, rfl⟩ := hab
    simp only [Fin.val_zero, Nat.cast_zero, kernelUnit_zero_row, cubicValue, lambdaValue_zero,
      xValue_zero, yValue_zero, zero_pow (by decide : 3 ≠ 0), zero_sub, neg_zero, add_zero, mul_zero]
    change iteratedDeriv 3 (fun _ : ℂ => (0 : ℂ)) 0 = 0
    exact iteratedDeriv_fun_const_zero

/-- The left third derivative is a finite transform of actual cubic and derivative values. -/
theorem unitSum_third (τ : ℍ) (r s : Fin N) :
    iteratedDeriv 3 (TorsionMuFourier.unitSum N τ r s) 0 =
      -(N : ℂ) ^ 3 * ∑ a : Fin N, ∑ b : Fin N,
        (cubicValue N (a : ℕ) (b : ℕ) τ + yValue N (a : ℕ) (b : ℕ) τ) *
          character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ) := by
  have hi (a : Fin N) : AnalyticAt ℂ (fun z : ℂ => ∑ b : Fin N,
      kernelUnit N (a : ℕ) (b : ℕ) τ z * character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) 0 :=
    Finset.analyticAt_fun_sum _ fun b _ =>
      (analyticAt_kernelUnit N (a : ℕ) (b : ℕ) τ).mul analyticAt_const
  change iteratedDeriv 3 (fun z : ℂ => -(N : ℂ) * ∑ a : Fin N, ∑ b : Fin N,
    kernelUnit N (a : ℕ) (b : ℕ) τ z * character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) 0 = _
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_fun_sum (fun a _ => (hi a).contDiffAt)]
  have hin (a : Fin N) : iteratedDeriv 3 (fun z : ℂ => ∑ b : Fin N,
      kernelUnit N (a : ℕ) (b : ℕ) τ z * character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) 0 =
      ∑ b : Fin N, (N : ℂ) ^ 2 * (cubicValue N (a : ℕ) (b : ℕ) τ + yValue N (a : ℕ) (b : ℕ) τ) *
        character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ) := by
    rw [iteratedDeriv_fun_sum (f := fun (b : Fin N) (z : ℂ) =>
      kernelUnit N (a : ℕ) (b : ℕ) τ z * character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ))
      (I := Finset.univ) (fun b _ =>
        ((analyticAt_kernelUnit N (a : ℕ) (b : ℕ) τ).mul analyticAt_const).contDiffAt)]
    exact Finset.sum_congr rfl fun b _ => by
      rw [iteratedDeriv_mul_const_field, kernelUnit_third_finite]
  simp_rw [hin, mul_assoc, ← Finset.mul_sum]
  ring

lemma third_z_mul {F : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) :
    iteratedDeriv 3 (fun z => z * F z) 0 = 3 * iteratedDeriv 2 F 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop) hF.contDiffAt]
  simp [Finset.sum_range_succ, iteratedDeriv_fun_id]

/-- The right ordinary analytic germ has third derivative 3N² times the actual WP′ value. -/
theorem rightGood_third (τ : ℍ) (r s : Fin N)
    (hg : ¬ ((N : ℤ) ∣ ((r : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((s : ℕ) : ℤ))) :
    iteratedDeriv 3 (TorsionMuFourier.rightGood N τ r s) 0 =
      3 * (N : ℂ) ^ 2 * yValue N (r : ℕ) (s : ℕ) τ := by
  let p := torsionPoint N (r : ℕ) (s : ℕ) τ
  let U := ThetaWeierstrass.unitLogDerivative (H τ) 0
  let L := logDeriv (H τ)
  have hp := H_torsion_ne_zero N (NeZero.pos N) τ (r : ℕ) (s : ℕ) hg
  have hu := ThetaWeierstrass.analyticAt_unitLogDerivative_zero τ
  have hu0 : AnalyticAt ℂ U ((N : ℂ) * 0) := by simpa only [mul_zero] using hu
  have hU : AnalyticAt ℂ (fun z : ℂ => U ((N : ℂ) * z)) 0 :=
    hu0.comp (f := fun z : ℂ => (N : ℂ) * z) (x := (0 : ℂ)) (by fun_prop)
  have hl : AnalyticAt ℂ L (0 + p) := by
    simpa only [zero_add, L, p, logDeriv, Pi.div_apply, ThetaWeierstrass.logDerivative] using!
      (ThetaWeierstrass.analyticAt_logDerivative (differentiable_H τ) hp)
  have hL : AnalyticAt ℂ (fun z : ℂ => L (z + p)) 0 :=
    hl.comp (f := fun z : ℂ => z + p) (x := (0 : ℂ)) (by fun_prop)
  have hU2 : iteratedDeriv 2 (fun z : ℂ => U ((N : ℂ) * z)) 0 = 0 := by
    simpa only [add_zero, unitLog_second_zero, mul_zero] using second_affine (N : ℂ) 0 hu
  have hL2 : iteratedDeriv 2 (fun z : ℂ => L (z + p)) 0 =
      -yValue N (r : ℕ) (s : ℕ) τ := by
    rw [iteratedDeriv_comp_add_const]
    simp only [zero_add]
    have h := wp_deriv_eq_neg_log_second τ hp
    change (ThetaWeierstrass.periodPair τ).derivWeierstrassP p = -iteratedDeriv 2 L p at h
    rw [yValue_of_good N (r : ℕ) (s : ℕ) τ hg]
    linear_combination h
  have he : TorsionMuFourier.rightGood N τ r s = (fun z : ℂ =>
      1 + (N : ℂ) * (z * U ((N : ℂ) * z)) -
      (2 * (Real.pi : ℂ) * I * (N : ℂ) * ((r : ℕ) : ℂ)) * z -
      (N : ℂ) ^ 2 * (z * L (z + p))) := by
    funext z
    unfold TorsionMuFourier.rightGood
    simp only [U, L, p, logDeriv, Pi.div_apply, ThetaWeierstrass.logDerivative]
    ring
  have hA : AnalyticAt ℂ (fun z : ℂ => 1 + (N : ℂ) * (z * U ((N : ℂ) * z))) 0 :=
    analyticAt_const.add (analyticAt_const.mul (analyticAt_id.mul hU))
  have hB : AnalyticAt ℂ (fun z : ℂ =>
      (2 * (Real.pi : ℂ) * I * (N : ℂ) * ((r : ℕ) : ℂ)) * z) 0 := by fun_prop
  have hC : AnalyticAt ℂ (fun z : ℂ => (N : ℂ) ^ 2 * (z * L (z + p))) 0 :=
    analyticAt_const.mul (analyticAt_id.mul hL)
  have hLin3 : iteratedDeriv 3 (fun z : ℂ =>
      (2 * (Real.pi : ℂ) * I * (N : ℂ) * ((r : ℕ) : ℂ)) * z) 0 = 0 := by
    rw [iteratedDeriv_const_mul_field]
    simp [iteratedDeriv_fun_id]
  rw [he]
  change iteratedDeriv 3 (((fun z : ℂ => 1 + (N : ℂ) * (z * U ((N : ℂ) * z))) -
    (fun z : ℂ => (2 * (Real.pi : ℂ) * I * (N : ℂ) * ((r : ℕ) : ℂ)) * z)) -
    (fun z : ℂ => (N : ℂ) ^ 2 * (z * L (z + p)))) 0 = _
  rw [iteratedDeriv_sub (hA.sub hB).contDiffAt hC.contDiffAt,
    iteratedDeriv_sub hA.contDiffAt hB.contDiffAt, hLin3, iteratedDeriv_const_add (by decide)]
  simp only [iteratedDeriv_const_mul_field]
  norm_num
  rw [third_z_mul hU, third_z_mul hL, hU2, hL2]
  ring

/-- The forward cubic/derivative transform is derived by differentiating an ordinary germ three times. -/
theorem forward_three_good (τ : ℍ) (r s : Fin N)
    (hg : ¬ ((N : ℤ) ∣ ((r : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((s : ℕ) : ℤ))) :
    (∑ a : Fin N, ∑ b : Fin N,
      (cubicValue N (a : ℕ) (b : ℕ) τ + yValue N (a : ℕ) (b : ℕ) τ) *
        character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) =
      -(3 / (N : ℂ)) * yValue N (r : ℕ) (s : ℕ) τ := by
  have h := (TorsionMuFourier.unitSum_germ_good N τ r s hg).iteratedDeriv_eq 3
  rw [unitSum_third, rightGood_third N τ r s hg] at h
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have h1 : (N : ℂ) * (∑ a : Fin N, ∑ b : Fin N,
      (cubicValue N (a : ℕ) (b : ℕ) τ + yValue N (a : ℕ) (b : ℕ) τ) *
        character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) =
      -3 * yValue N (r : ℕ) (s : ℕ) τ := by
    apply mul_left_cancel₀ (pow_ne_zero 2 hn)
    linear_combination -h
  apply mul_left_cancel₀ hn
  field_simp [hn]
  linear_combination h1

/-- Finite reindexing for any genuinely odd, representative-independent torsion value. -/
theorem finite_sum_odd (f : ℤ → ℤ → ℂ)
    (hshift : ∀ a b m n, f (a + (N : ℤ) * m) (b + (N : ℤ) * n) = f a b)
    (hodd : ∀ a b, f (-a) (-b) = -f a b) :
    (∑ p : Fin N × Fin N, f (p.1 : ℕ) (p.2 : ℕ)) = 0 := by
  let F : TorsionCorrelation.Point N → ℂ := fun P => f (P.1.val : ℤ) (P.2.val : ℤ)
  have hl (a b c d : ℤ) (he : TorsionCorrelation.label N a b = TorsionCorrelation.label N c d) :
      f a b = f c d := by
    have ha : (N : ℤ) ∣ a - c :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub c a N).mp (congrArg Prod.fst he).symm
    have hb : (N : ℤ) ∣ b - d :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub d b N).mp (congrArg Prod.snd he).symm
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    rw [show a = c + (N : ℤ) * m by linarith, show b = d + (N : ℤ) * n by linarith, hshift]
  have hlabel (a b : ℤ) : F (TorsionCorrelation.label N a b) = f a b :=
    hl _ _ a b (TorsionCorrelation.label_val (NeZero.pos N) (TorsionCorrelation.label N a b))
  have hneg (P : TorsionCorrelation.Point N) : F (-P) = -F P := by
    obtain ⟨a, b, rfl⟩ := TorsionCorrelation.label_surjective (NeZero.pos N) P
    rw [TorsionCorrelation.label_neg, hlabel, hlabel, hodd]
  have h := Equiv.sum_comp (Equiv.neg (TorsionCorrelation.Point N)) F
  simp only [Equiv.neg_apply, hneg, Finset.sum_neg_distrib] at h
  have hs : (∑ P : TorsionCorrelation.Point N, F P) = 0 := by linear_combination -h / 2
  let e : (Fin N × Fin N) ≃ TorsionCorrelation.Point N :=
    Equiv.prodCongr (ZMod.finEquiv N).toEquiv (ZMod.finEquiv N).toEquiv
  have heq : (∑ p : Fin N × Fin N, f (p.1 : ℕ) (p.2 : ℕ)) =
      ∑ P : TorsionCorrelation.Point N, F P := by
    apply Fintype.sum_equiv e
    intro p
    cases N with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ n => rfl
  rw [heq, hs]

omit [NeZero N] in
lemma xValue_neg (a b : ℤ) (τ : ℍ) : xValue N (-a) (-b) τ = xValue N a b τ := by
  by_cases hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · have hb' : (N : ℤ) ∣ -a ∧ (N : ℤ) ∣ -b := by simpa using hb
    simp only [xValue, ite_eq_left hb, ite_eq_left hb']
  · have hb' : ¬ ((N : ℤ) ∣ -a ∧ (N : ℤ) ∣ -b) := by simpa using hb
    rw [xValue_of_good N (-a) (-b) τ hb', xValue_of_good N a b τ hb]
    have he : torsionPoint N (-a) (-b) τ = -torsionPoint N a b τ := by
      unfold torsionPoint
      push_cast
      ring
    rw [he, PeriodPair.weierstrassP_neg]

lemma cubicValue_neg (a b : ℤ) (τ : ℍ) : cubicValue N (-a) (-b) τ = -cubicValue N a b τ := by
  have hl : lambdaValue N (-a) (-b) τ = -lambdaValue N a b τ := by
    unfold lambdaValue
    rw [TorsionFourierComparison.reg_neg]
    ring
  rw [cubicValue, cubicValue, hl, xValue_neg]
  ring

lemma cubicValue_shift (a b m n : ℤ) (τ : ℍ) :
    cubicValue N (a + N * m) (b + N * n) τ = cubicValue N a b τ := by
  unfold cubicValue lambdaValue
  rw [TorsionFourierComparison.reg_shift, WeierstrassDistributionNat.xValue_shift (NeZero.pos N)]

/-- The zero row is fixed by actual oddness, not by assigning a residue at zero. -/
theorem forward_three_finite (τ : ℍ) (r s : Fin N) :
    (∑ a : Fin N, ∑ b : Fin N,
      (cubicValue N (a : ℕ) (b : ℕ) τ + yValue N (a : ℕ) (b : ℕ) τ) *
        character N (a : ℕ) (b : ℕ) (r : ℕ) (s : ℕ)) =
      -(3 / (N : ℂ)) * yValue N (r : ℕ) (s : ℕ) τ := by
  by_cases hg : ¬ ((N : ℤ) ∣ ((r : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((s : ℕ) : ℤ))
  · exact forward_three_good N τ r s hg
  · have hrs : r = 0 ∧ s = 0 := by
      have h := (finite_good_iff N r s).not.mp hg
      tauto
    obtain ⟨rfl, rfl⟩ := hrs
    have hsum := finite_sum_odd N (fun a b => cubicValue N a b τ + yValue N a b τ)
      (fun a b m n => by rw [cubicValue_shift, yValue_shift N (NeZero.pos N)])
      (fun a b => by rw [cubicValue_neg, yValue_neg N (NeZero.pos N)]; ring)
    simpa [character, Fintype.sum_prod_type, yValue_zero] using hsum

/-- The nonvanishing denominator for the finite cubic inversion holds at every positive integer level. -/
theorem cubic_denominator_ne_zero (N : ℕ) (hN : 0 < N) : (N : ℂ) ^ 4 - 9 ≠ 0 := by
  by_cases h1 : N = 1
  · subst N
    norm_num
  · have h2 : 2 ≤ N := by omega
    have hr : (2 : ℝ) ≤ N := by exact_mod_cast h2
    have hs : (4 : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h : (N : ℝ) ^ 4 - 9 ≠ 0 := by nlinarith [sq_nonneg ((N : ℝ) ^ 2 - 4)]
    exact_mod_cast h

/-- Finite inversion gives the actual derivative value in terms of actual cubic products. -/
theorem yValue_cubic_formula_finite (τ : ℍ) (r s : Fin N) :
    yValue N (r : ℕ) (s : ℕ) τ =
      (3 * (N : ℂ) * ∑ p : Fin N × Fin N, cubicValue N (p.1 : ℕ) (p.2 : ℕ) τ *
          TorsionMuFourier.chi N p (r, s) -
        (N : ℂ) ^ 4 * cubicValue N (r : ℕ) (s : ℕ) τ) / ((N : ℂ) ^ 4 - 9) := by
  let A : Fin N × Fin N → ℂ := fun p => cubicValue N (p.1 : ℕ) (p.2 : ℕ) τ
  let Y : Fin N × Fin N → ℂ := fun p => yValue N (p.1 : ℕ) (p.2 : ℕ) τ
  let F := TorsionMuFourier.transform N
  have hF (p : Fin N × Fin N) : F Y p = -(3 / (N : ℂ)) * Y p - F A p := by
    have h : F (fun q => A q + Y q) p = -(3 / (N : ℂ)) * Y p := by
      simpa only [F, A, Y, TorsionMuFourier.transform, TorsionMuFourier.chi,
        Fintype.sum_prod_type] using forward_three_finite N τ p.1 p.2
    have he : F (fun q => A q + Y q) p = F A p + F Y p := by
      simp only [F, TorsionMuFourier.transform, add_mul, Finset.sum_add_distrib]
    rw [he] at h
    linear_combination h
  have hFF := TorsionMuFourier.transform_square N Y (r, s)
  have hFA := TorsionMuFourier.transform_square N A (r, s)
  change F (F Y) (r, s) = (N : ℂ) ^ 2 * Y (r, s) at hFF
  change F (F A) (r, s) = (N : ℂ) ^ 2 * A (r, s) at hFA
  have hrec : F (F Y) (r, s) = -(3 / (N : ℂ)) * F Y (r, s) - F (F A) (r, s) := by
    have he : F Y = fun p => -(3 / (N : ℂ)) * Y p - F A p := funext hF
    conv_lhs => rw [he]
    change (∑ p : Fin N × Fin N, (-(3 / (N : ℂ)) * Y p - F A p) * TorsionMuFourier.chi N p (r, s)) = _
    simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    rfl
  rw [hFF, hFA, hF] at hrec
  change Y (r, s) = (3 * (N : ℂ) * F A (r, s) - (N : ℂ) ^ 4 * A (r, s)) /
    ((N : ℂ) ^ 4 - 9)
  apply (eq_div_iff (cubic_denominator_ne_zero N (NeZero.pos N))).mpr
  have hn : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  field_simp [hn] at hrec
  linear_combination hrec

/-- Every integer label has a genuine finite representative and an integral level shift. -/
lemma integer_row_representative (r : ℤ) :
    ∃ R : Fin N, ∃ m : ℤ, r = ((R : ℕ) : ℤ) + (N : ℤ) * m := by
  have hn0 : (N : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hn : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
  let R : Fin N := ⟨(r % (N : ℤ)).toNat, by
    have h0 := Int.emod_nonneg r hn0
    have h1 := Int.emod_lt_of_pos r hn
    omega⟩
  have hR : ((R : ℕ) : ℤ) = r % (N : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg r hn0)
  refine ⟨R, r / (N : ℤ), ?_⟩
  rw [hR]
  exact (Int.emod_add_mul_ediv r (N : ℤ)).symm

/-- All integer labels, including negative and bad classes, satisfy the actual cubic formula. -/
theorem yValue_cubic_formula (τ : ℍ) (r s : ℤ) :
    yValue N r s τ =
      (3 * (N : ℂ) * ∑ p : Fin N × Fin N, cubicValue N (p.1 : ℕ) (p.2 : ℕ) τ *
          character N (p.1 : ℕ) (p.2 : ℕ) r s - (N : ℂ) ^ 4 * cubicValue N r s τ) /
        ((N : ℂ) ^ 4 - 9) := by
  obtain ⟨R, m, hr⟩ := integer_row_representative N r
  obtain ⟨S, n, hs⟩ := integer_row_representative N s
  rw [hr, hs, yValue_shift N (NeZero.pos N), cubicValue_shift]
  simp_rw [TorsionFourierComparison.character_shift]
  exact yValue_cubic_formula_finite N τ R S

/-- The ordinary analytic third jet of the actual kernel, with a proved analytic remainder. -/
theorem kernel_third_laurent (a b : ℤ) (τ : ℍ)
    (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    ∃ R : ℂ → ℂ, AnalyticAt ℂ R 0 ∧ ∀ᶠ z in 𝓝[≠] (0 : ℂ), H τ ((N : ℂ) * z) ≠ 0 ∧
      TorsionFourierKernel.kernel N a b τ z = 1 / ((N : ℂ) * z) + lambdaValue N a b τ +
        (N : ℂ) * muValue N a b τ * z +
        ((N : ℂ) ^ 2 / 6) * (cubicValue N a b τ + yValue N a b τ) * z ^ 2 + z ^ 3 * R z := by
  obtain ⟨R, hR, he⟩ := (analyticAt_kernelUnit N a b τ).exists_eventuallyEq_sum_add_pow_mul 4
  have hTaylor : ∀ᶠ z in 𝓝 (0 : ℂ), kernelUnit N a b τ z =
      (N : ℂ)⁻¹ + lambdaValue N a b τ * z + (N : ℂ) * muValue N a b τ * z ^ 2 +
        ((N : ℂ) ^ 2 / 6) * (cubicValue N a b τ + yValue N a b τ) * z ^ 3 + z ^ 4 * R z := by
    filter_upwards [he] with z hz
    simp only [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
      kernelUnit_zero N a b τ hg, kernelUnit_deriv_zero N a b τ hg,
      kernelUnit_second_zero N a b τ hg, kernelUnit_third_zero N a b τ hg, smul_eq_mul] at hz
    norm_num at hz
    convert hz using 1
    ring
  have hn := (differentiable_unitDenominator N τ 0).continuousAt.eventually_ne
    (unitDenominator_zero_ne N τ)
  refine ⟨R, hR, ?_⟩
  filter_upwards [hTaylor.filter_mono nhdsWithin_le_nhds,
    hn.filter_mono nhdsWithin_le_nhds, kernelUnit_germ N a b τ, self_mem_nhdsWithin]
    with z hz hdz hez hzne
  have hz0 : z ≠ 0 := hzne
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  refine ⟨?_, ?_⟩
  · rw [dilated_factorization]
    exact mul_ne_zero hz0 hdz
  · calc
      TorsionFourierKernel.kernel N a b τ z = kernelUnit N a b τ z / z := by
        apply (eq_div_iff hz0).mpr
        simpa only [mul_comm] using hez
      _ = _ := by
        rw [hz]
        field_simp [hz0, hN]

end ZInQ.Contrib.HeckePrimeRationality.TorsionWeightThree
