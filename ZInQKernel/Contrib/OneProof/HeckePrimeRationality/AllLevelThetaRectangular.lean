import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.RectangularThetaAnalytic
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelThetaMultiplicationTwo
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionDistributionNat
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionDistributionNatRegular

/-!
# Actual rectangular theta isogeny and torsion identities

The real-grid product is compared with the actual completed theta at nτ by
its zeros, simple denominator zeros, exact automorphy and Liouville. Its
logarithmic derivative gives a genuine rectangular torsion identity on Good
labels. The reciprocal rectangular identity follows from the proved S law.
-/

noncomputable section

open Complex Set Function Filter Finset
open scoped Real UpperHalfPlane BigOperators Topology MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.ThetaRectangular

open CompletedTheta RectangularThetaLattice

local notation "κ" => ((Real.pi : ℂ) * Complex.I)

/-- The actual completed theta for the rectangular target lattice. -/
def realTarget (n : ℕ) (hn : 0 < n) (τ : ℍ) (z : ℂ) : ℂ :=
  H (upTau n hn τ) ((n : ℂ) * z)

lemma realTarget_differentiable (n : ℕ) (hn : 0 < n) (τ : ℍ) :
    Differentiable ℂ (realTarget n hn τ) := by
  unfold realTarget
  exact (differentiable_H _).fun_comp (differentiable_id.const_mul _)

lemma realTarget_one (n : ℕ) (hn : 0 < n) (τ : ℍ) (z : ℂ) :
    realTarget n hn τ (z+1) = (-1 : ℂ)^n * realTarget n hn τ z := by
  unfold realTarget
  rw [show (n : ℂ) * (z+1) = (n : ℂ) * z + (n : ℂ) by ring]
  exact quasi_nat_one (H_add_one _) n _

lemma realTarget_tau (n : ℕ) (hn : 0 < n) (τ : ℍ) (z : ℂ) :
    realTarget n hn τ (z+(τ : ℂ)) =
      -cexp (-κ*(n : ℂ)*(τ : ℂ)-2*κ*(n : ℂ)*z) * realTarget n hn τ z := by
  unfold realTarget
  rw [show (n : ℂ)*(z+(τ : ℂ)) = (n : ℂ)*z+(upTau n hn τ : ℂ) by rw [upTau_coe]; ring]
  simpa only [upTau_coe,mul_assoc,neg_mul] using H_add_tau (upTau n hn τ) ((n : ℂ)*z)

/-- The actual numerator and target have the same rectangular zero set. -/
theorem realProduct_target_zero (n : ℕ) (hn : 0 < n) (τ : ℍ) (z : ℂ) :
    realProduct n (H τ) z = 0 ↔ realTarget n hn τ z = 0 := by
  rw [realProduct_zero_iff hn τ (H_zero_iff_lattice τ), realTarget, H_zero_iff_lattice, upTau_coe]

lemma realTarget_deriv (n : ℕ) (hn : 0 < n) (τ : ℍ) (z : ℂ) :
    deriv (realTarget n hn τ) z = deriv (H (upTau n hn τ)) ((n : ℂ)*z) * (n : ℂ) := by
  have hl : HasDerivAt (fun w : ℂ => (n : ℂ)*w) (n : ℂ) z := by
    simpa using! (hasDerivAt_id z).const_mul (n : ℂ)
  simpa only [realTarget, Function.comp_def] using!
    ((differentiable_H _ _).hasDerivAt.comp z hl).deriv

/-- Every zero of the rectangular target is simple, by the actual H derivative. -/
theorem realTarget_simple (n : ℕ) (hn : 0 < n) (τ : ℍ) {z : ℂ}
    (hz : realTarget n hn τ z = 0) : deriv (realTarget n hn τ) z ≠ 0 := by
  have hd : deriv (H (upTau n hn τ)) ((n : ℂ)*z) ≠ 0 :=
    QuasiThetaMultiplicationTwo.deriv_ne_zero_at_zero (differentiable_H _) (H_add_one _)
      (fun w => by simpa only [mul_assoc, neg_mul] using H_add_tau (upTau n hn τ) w)
      (H_zero_iff_lattice _) (deriv_H_zero_ne_zero _) hz
  rw [realTarget_deriv]
  exact mul_ne_zero hd (by exact_mod_cast hn.ne')

/-- Genuine one-dimensional real-grid multiplication for the actual completed theta.
No rectangular identity or quotient constancy is assumed. -/
theorem H_real_multiplication (n : ℕ) (hn : 0 < n) (τ : ℍ) :
    ∃ C : ℂ, C ≠ 0 ∧ ∀ z : ℂ,
      (∏ b : Fin n, H τ (z+(b : ℂ)/(n : ℂ))) = C * H (upTau n hn τ) ((n : ℂ)*z) := by
  have hkd (z : ℂ) (hz : H (upTau n hn τ) z=0) : deriv (H (upTau n hn τ)) z≠0 :=
    QuasiThetaMultiplicationTwo.deriv_ne_zero_at_zero (differentiable_H _) (H_add_one _)
      (fun w => by simpa only [mul_assoc,neg_mul] using H_add_tau (upTau n hn τ) w)
      (H_zero_iff_lattice _) (deriv_H_zero_ne_zero _) hz
  have hh := RectangularThetaAnalytic.real_multiplication n hn τ (H τ) (H (upTau n hn τ))
    (differentiable_H τ) (differentiable_H _) (H_add_one τ)
    (fun z => by simpa only [mul_assoc,neg_mul] using H_add_tau τ z) (H_add_one _)
    (fun z => by simpa only [mul_assoc,neg_mul] using H_add_tau (upTau n hn τ) z)
    (H_zero_iff_lattice τ) (H_zero_iff_lattice _) hkd
  exact hh

/-- Genuine imaginary rectangular multiplication for the actual completed theta,
with its explicitly derived compensating phase and equality at all zeros. -/
theorem H_imag_multiplication (n : ℕ) (hn : 0<n) (τ : ℍ) :
    ∃ C : ℂ,C≠0 ∧ ∀ z : ℂ,
      (∏ a : Fin n,H τ (z+(a : ℂ)*(τ : ℂ)/(n : ℂ))) =
        C*cexp (-κ*((n-1 : ℕ) : ℂ)*z)*H (downTau n hn τ) z := by
  have hkd (z : ℂ) (hz : H (downTau n hn τ) z=0) : deriv (H (downTau n hn τ)) z≠0 :=
    QuasiThetaMultiplicationTwo.deriv_ne_zero_at_zero (differentiable_H _) (H_add_one _)
      (fun w => by simpa only [mul_assoc,neg_mul] using H_add_tau (downTau n hn τ) w)
      (H_zero_iff_lattice _) (deriv_H_zero_ne_zero _) hz
  exact RectangularThetaAnalytic.imag_multiplication n hn τ (H τ) (H (downTau n hn τ))
    (differentiable_H τ) (differentiable_H _) (H_add_one τ)
    (fun z => by simpa only [mul_assoc,neg_mul] using H_add_tau τ z) (H_add_one _)
    (fun z => by simpa only [mul_assoc,neg_mul] using H_add_tau (downTau n hn τ) z)
    (H_zero_iff_lattice τ) (H_zero_iff_lattice _) hkd

/-- Logarithmic differentiation is performed only where all actual factors are nonzero. -/
theorem real_logDeriv (n : ℕ) (hn : 0 < n) (τ : ℍ) (z : ℂ)
    (hgood : ∀ b : Fin n, H τ (z+(b : ℂ)/n) ≠ 0)
    (himage : H (upTau n hn τ) ((n : ℂ)*z) ≠ 0) :
    (∑ b : Fin n, Hder τ (z+(b : ℂ)/n) / H τ (z+(b : ℂ)/n)) =
      (n : ℂ) * (Hder (upTau n hn τ) ((n : ℂ)*z) / H (upTau n hn τ) ((n : ℂ)*z)) := by
  obtain ⟨C,hC,hid⟩ := H_real_multiplication n hn τ
  have hl := TorsionDistributionNat.hasDerivAt_prod_logDeriv
    (f := fun b : Fin n => fun w : ℂ => H τ (w+(b : ℂ)/n))
    (fun b => (hasDerivAt_H τ (z+(b : ℂ)/n)).comp_add_const z _) hgood
  have hnlin : HasDerivAt (fun w : ℂ => (n : ℂ)*w) (n : ℂ) z := by
    simpa using! (hasDerivAt_id z).const_mul (n : ℂ)
  have hr : HasDerivAt (fun w : ℂ => C * H (upTau n hn τ) ((n : ℂ)*w))
      (C * (Hder (upTau n hn τ) ((n : ℂ)*z) * (n : ℂ))) z := by
    simpa only [Function.comp_def] using! ((hasDerivAt_H _ _).comp z hnlin).const_mul C
  have hhr := hr.congr_of_eventuallyEq (Eventually.of_forall hid)
  have he := hl.unique hhr
  rw [hid z] at he
  have he' : C * (H (upTau n hn τ) ((n : ℂ)*z) *
      (∑ b : Fin n, Hder τ (z+(b : ℂ)/n) / H τ (z+(b : ℂ)/n))) =
      C * (Hder (upTau n hn τ) ((n : ℂ)*z) * (n : ℂ)) := by
    simpa only [mul_assoc] using he
  have hh := mul_left_cancel₀ hC he'
  calc
    _ = (Hder (upTau n hn τ) ((n : ℂ)*z)*(n : ℂ))/H (upTau n hn τ) ((n : ℂ)*z) := by
      apply (eq_div_iff himage).mpr
      simpa only [mul_comm] using hh
    _ = _ := by ring

/-- Good labels have Good preimages in the real rectangular direction. -/
lemma good_real_lift {n N : ℕ} (hn : 0 < n) {r s : ℤ}
    (hg : ¬ ((N : ℤ)∣r ∧ (N : ℤ)∣s)) (b : Fin n) :
    ¬ (((n*N : ℕ) : ℤ)∣(n : ℤ)*r ∧ ((n*N : ℕ) : ℤ)∣s+(N : ℤ)*(b : ℕ)) := by
  have hnZ : (n : ℤ)≠0 := by exact_mod_cast hn.ne'
  rintro ⟨hr,hs⟩
  apply hg
  have hNr : (N : ℤ)∣r := by
    push_cast at hr
    exact (mul_dvd_mul_iff_left hnZ).mp hr
  have hd : (N : ℤ)∣((n*N : ℕ) : ℤ) := by exact ⟨n,by push_cast; ring⟩
  have hNs : (N : ℤ)∣s := (dvd_add_left (dvd_mul_right _ _)).mp (hd.trans hs)
  exact ⟨hNr,hNs⟩

lemma real_torsion_point (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (r s : ℤ) (b : Fin n) :
    torsionPoint (n*N) ((n : ℤ)*r) (s+(N : ℤ)*(b : ℕ)) τ =
      torsionPoint N r s (upTau n hn τ)/(n : ℂ)+(b : ℂ)/(n : ℂ) := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  have hNC : (N : ℂ)≠0 := by exact_mod_cast hN.ne'
  unfold torsionPoint
  rw [upTau_coe]
  push_cast
  field_simp [hnC,hNC]
  ring

/-- Genuine rectangular rational-scaling identity on Good actual torsion labels. -/
theorem raw_up (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (r s : ℤ)
    (hg : ¬ ((N : ℤ)∣r ∧ (N : ℤ)∣s)) :
    Torsion.torsionLogDerivative N r s (upTau n hn τ) =
      (1/(n : ℂ)) * ∑ b : Fin n,
        Torsion.torsionLogDerivative (n*N) ((n : ℤ)*r) (s+(N : ℤ)*(b : ℕ)) τ := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  have hNC : (N : ℂ)≠0 := by exact_mod_cast hN.ne'
  let u : ℂ := torsionPoint N r s (upTau n hn τ)/(n : ℂ)
  have hnu : (n : ℂ)*u = torsionPoint N r s (upTau n hn τ) := by dsimp [u]; field_simp [hnC]
  have hp (b : Fin n) : H τ (u+(b : ℂ)/n) ≠ 0 := by
    rw [← real_torsion_point n N hn hN τ r s b]
    exact H_torsion_ne_zero (n*N) (Nat.mul_pos hn hN) τ _ _ (good_real_lift hn hg b)
  have hi : H (upTau n hn τ) ((n : ℂ)*u) ≠0 := by
    rw [hnu]
    exact H_torsion_ne_zero N hN _ _ _ hg
  have hl := real_logDeriv n hn τ u hp hi
  rw [hnu] at hl
  have ht (b : Fin n) :
      Torsion.torsionLogDerivative (n*N) ((n : ℤ)*r) (s+(N : ℤ)*(b : ℕ)) τ =
        (r : ℂ)/(N : ℂ) + (Hder τ (u+(b : ℂ)/n)/H τ (u+(b : ℂ)/n))/(2*κ) := by
    rw [torsionLogDerivative_eq (n*N) (Nat.mul_pos hn hN) τ _ _ (good_real_lift hn hg b),
      real_torsion_point n N hn hN τ r s b]
    push_cast
    change ((n : ℂ)*(r : ℂ))/((n : ℂ)*(N : ℂ)) +
      Hder τ (u+(b : ℂ)/n)/(2*(Real.pi : ℂ)*I*H τ (u+(b : ℂ)/n)) =
        (r : ℂ)/(N : ℂ)+(Hder τ (u+(b : ℂ)/n)/H τ (u+(b : ℂ)/n))/(2*κ)
    have hcoeff : ((n : ℂ)*(r : ℂ))/((n : ℂ)*(N : ℂ))=(r : ℂ)/(N : ℂ) := by
      field_simp [hnC,hNC]
    rw [hcoeff,div_div,show 2*(Real.pi : ℂ)*I*H τ (u+(b : ℂ)/n)=H τ (u+(b : ℂ)/n)*(2*κ) by ring]
  rw [torsionLogDerivative_eq N hN _ r s hg]
  simp_rw [ht,Finset.sum_add_distrib,← Finset.sum_div]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [hl]
  field_simp [hnC,hNC,hi]

/-- The real rectangular identity in the unchanged Good zero-extended family. -/
theorem reg_up_good (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (r s : ℤ)
    (hg : ¬ ((N : ℤ)∣r ∧ (N : ℤ)∣s)) :
    TorsionDistributionTwo.reg N r s (upTau n hn τ) =
      (1/(n : ℂ)) * ∑ b : Fin n, TorsionDistributionTwo.reg (n*N) ((n : ℤ)*r) (s+(N : ℤ)*(b : ℕ)) τ := by
  rw [TorsionDistributionTwo.reg_of_good hg]
  simp_rw [TorsionDistributionTwo.reg_of_good (good_real_lift hn hg _)]
  exact raw_up n N hn hN τ r s hg

lemma good_imag_lift {n N : ℕ} (hn : 0 < n) {r s : ℤ}
    (hg : ¬ ((N : ℤ)∣r ∧ (N : ℤ)∣s)) (a : Fin n) :
    ¬ (((n*N : ℕ) : ℤ)∣r+(N : ℤ)*(a : ℕ) ∧ ((n*N : ℕ) : ℤ)∣(n : ℤ)*s) := by
  have hnZ : (n : ℤ)≠0 := by exact_mod_cast hn.ne'
  have hd : (N : ℤ)∣((n*N : ℕ) : ℤ) := ⟨n,by push_cast; ring⟩
  rintro ⟨hr,hs⟩
  apply hg
  refine ⟨(dvd_add_left (dvd_mul_right _ _)).mp (hd.trans hr), ?_⟩
  push_cast at hs
  exact (mul_dvd_mul_iff_left hnZ).mp hs

/-- Scaling and the actual inversion S commute in the required reciprocal direction. -/
lemma upTau_S (n : ℕ) (hn : 0 < n) (τ : ℍ) :
    upTau n hn (ModularGroup.S • τ) = ModularGroup.S • downTau n hn τ := by
  apply UpperHalfPlane.ext
  rw [upTau_coe, ThetaFive.coe_S_smul, ThetaFive.coe_S_smul, downTau_coe]
  field_simp [τ.ne_zero, show (n : ℂ)≠0 by exact_mod_cast hn.ne']

/-- The reciprocal rectangular identity is derived from real-grid multiplication
and the proved actual S-covariance, not square-grid distribution. -/
theorem raw_down (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (r s : ℤ)
    (hg : ¬ ((N : ℤ)∣r ∧ (N : ℤ)∣s)) :
    Torsion.torsionLogDerivative N r s (downTau n hn τ) =
      ∑ a : Fin n, Torsion.torsionLogDerivative (n*N) (r+(N : ℤ)*(a : ℕ)) ((n : ℤ)*s) τ := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  have htau : (τ : ℂ)≠0 := τ.ne_zero
  have hrot : ¬ ((N : ℤ)∣-s ∧ (N : ℤ)∣r) := by
    rintro ⟨hs,hr⟩
    exact hg ⟨hr,(dvd_neg).mp hs⟩
  have hh := raw_up n N hn hN (ModularGroup.S • τ) (-s) r hrot
  rw [upTau_S] at hh
  have hleft : Torsion.torsionLogDerivative N (-s) r (ModularGroup.S • downTau n hn τ) =
      (downTau n hn τ : ℂ) * Torsion.torsionLogDerivative N r s (downTau n hn τ) := by
    simpa only [AllLevelForms.F,neg_neg] using
      (AllLevelForms.F_S hN (a := -s) (b := r) (by simpa only [AllLevelForms.Good,neg_neg] using hg) (downTau n hn τ))
  have hright (a : Fin n) :
      Torsion.torsionLogDerivative (n*N) ((n : ℤ)*(-s)) (r+(N : ℤ)*(a : ℕ)) (ModularGroup.S • τ) =
      (τ : ℂ) * Torsion.torsionLogDerivative (n*N) (r+(N : ℤ)*(a : ℕ)) ((n : ℤ)*s) τ := by
    have hg' : AllLevelForms.Good (n*N) (r+(N : ℤ)*(a : ℕ), -((n : ℤ)*(-s))) := by
      simpa only [AllLevelForms.Good,mul_neg,neg_neg] using good_imag_lift hn hg a
    simpa only [AllLevelForms.F,mul_neg,neg_neg] using
      AllLevelForms.F_S (Nat.mul_pos hn hN) (a := (n : ℤ)*(-s)) (b := r+(N : ℤ)*(a : ℕ)) hg' τ
  rw [hleft] at hh
  simp_rw [hright] at hh
  rw [← Finset.mul_sum, downTau_coe] at hh
  field_simp [hnC,htau] at hh
  exact hh

/-- The reciprocal rectangular formula in the unchanged Good reg family. -/
theorem reg_down_good (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (r s : ℤ)
    (hg : ¬ ((N : ℤ)∣r ∧ (N : ℤ)∣s)) :
    TorsionDistributionTwo.reg N r s (downTau n hn τ) =
      ∑ a : Fin n, TorsionDistributionTwo.reg (n*N) (r+(N : ℤ)*(a : ℕ)) ((n : ℤ)*s) τ := by
  rw [TorsionDistributionTwo.reg_of_good hg]
  have hterm (a : Fin n) := TorsionDistributionTwo.reg_of_good (good_imag_lift hn hg a) τ
  simp_rw [hterm]
  exact raw_down n N hn hN τ r s hg

lemma cyclic_odd_cancel (n : ℕ) (g : ℤ → ℂ) (hper : ∀ x,g (x+(n : ℤ))=g x)
    (hodd : ∀ x,g (-x)=-g x) (c : ℤ) : (∑ b : Fin n,g ((b : ℤ)+c))=0 := by
  rw [Fin.sum_univ_eq_sum_range (fun b : ℕ => g ((b : ℤ)+c)) n,
    AllLevelAverage.sum_range_shift g hper c]
  have hn := TorsionDistributionNat.sum_range_neg g hper
  simp_rw [hodd,Finset.sum_neg_distrib] at hn
  linear_combination (-1/2 : ℂ)*hn

/-- The real rectangular sum at a bad original class vanishes by actual periodic oddness. -/
lemma real_bad_sum (n N : ℕ) (hn : 0<n) (hN : 0<N) (τ : ℍ) (r s : ℤ)
    (hb : (N : ℤ)∣r ∧ (N : ℤ)∣s) :
    (∑ b : Fin n,TorsionDistributionTwo.reg (n*N) ((n : ℤ)*r) (s+(N : ℤ)*(b : ℕ)) τ)=0 := by
  obtain ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩ := hb
  have hpos := Nat.mul_pos hn hN
  let g : ℤ → ℂ := fun x => TorsionDistributionTwo.reg (n*N) 0 ((N : ℤ)*x) τ
  have hp (x : ℤ) : g (x+(n : ℤ))=g x := by
    have hh := TorsionDistributionNat.reg_shift hpos 0 ((N : ℤ)*x) 0 1 τ
    simpa only [g,Nat.cast_mul,mul_zero,zero_add,mul_one,mul_add,add_mul,mul_comm] using hh
  have ho (x : ℤ) : g (-x)=-g x := by
    have hh := TorsionDistributionNat.reg_neg hpos 0 ((N : ℤ)*x) τ
    simpa only [g,neg_zero,mul_neg] using hh
  have ht (b : Fin n) : TorsionDistributionTwo.reg (n*N) ((n : ℤ)*((N : ℤ)*u))
      ((N : ℤ)*v+(N : ℤ)*(b : ℕ)) τ=g ((b : ℤ)+v) := by
    rw [show (n : ℤ)*((N : ℤ)*u)=0+((n*N : ℕ) : ℤ)*u by push_cast;ring,
      show (N : ℤ)*v+(N : ℤ)*(b : ℕ)=(N : ℤ)*((b : ℤ)+v)+((n*N : ℕ) : ℤ)*0 by ring,
      TorsionDistributionNat.reg_shift hpos]
  simp_rw [ht]
  exact cyclic_odd_cancel n g hp ho v

/-- The imaginary rectangular sum at a bad original class has the same actual cancellation. -/
lemma imag_bad_sum (n N : ℕ) (hn : 0<n) (hN : 0<N) (τ : ℍ) (r s : ℤ)
    (hb : (N : ℤ)∣r ∧ (N : ℤ)∣s) :
    (∑ a : Fin n,TorsionDistributionTwo.reg (n*N) (r+(N : ℤ)*(a : ℕ)) ((n : ℤ)*s) τ)=0 := by
  obtain ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩ := hb
  have hpos := Nat.mul_pos hn hN
  let g : ℤ → ℂ := fun x => TorsionDistributionTwo.reg (n*N) ((N : ℤ)*x) 0 τ
  have hp (x : ℤ) : g (x+(n : ℤ))=g x := by
    have hh := TorsionDistributionNat.reg_shift hpos ((N : ℤ)*x) 0 1 0 τ
    simpa only [g,Nat.cast_mul,mul_zero,zero_add,mul_one,mul_add,add_mul,mul_comm] using hh
  have ho (x : ℤ) : g (-x)=-g x := by
    have hh := TorsionDistributionNat.reg_neg hpos ((N : ℤ)*x) 0 τ
    simpa only [g,neg_zero,mul_neg] using hh
  have ht (a : Fin n) : TorsionDistributionTwo.reg (n*N) ((N : ℤ)*u+(N : ℤ)*(a : ℕ))
      ((n : ℤ)*((N : ℤ)*v)) τ=g ((a : ℤ)+u) := by
    rw [show (N : ℤ)*u+(N : ℤ)*(a : ℕ)=(N : ℤ)*((a : ℤ)+u)+((n*N : ℕ) : ℤ)*0 by ring,
      show (n : ℤ)*((N : ℤ)*v)=0+((n*N : ℕ) : ℤ)*v by push_cast;ring,
      TorsionDistributionNat.reg_shift hpos]
  simp_rw [ht]
  exact cyclic_odd_cancel n g hp ho u

/-- All-label real rectangular distribution in the unchanged actual zero extension. -/
theorem reg_up (n N : ℕ) (hn : 0<n) (hN : 0<N) (τ : ℍ) (r s : ℤ) :
    TorsionDistributionTwo.reg N r s (upTau n hn τ)=
      (1/(n : ℂ))*∑ b : Fin n,TorsionDistributionTwo.reg (n*N) ((n : ℤ)*r) (s+(N : ℤ)*(b : ℕ)) τ := by
  by_cases hb : (N : ℤ)∣r ∧ (N : ℤ)∣s
  · rw [TorsionDistributionTwo.reg_of_bad hb,real_bad_sum n N hn hN τ r s hb,mul_zero]
  · exact reg_up_good n N hn hN τ r s hb

/-- All-label reciprocal rectangular distribution, with separately proved bad-class cancellation. -/
theorem reg_down (n N : ℕ) (hn : 0<n) (hN : 0<N) (τ : ℍ) (r s : ℤ) :
    TorsionDistributionTwo.reg N r s (downTau n hn τ)=
      ∑ a : Fin n,TorsionDistributionTwo.reg (n*N) (r+(N : ℤ)*(a : ℕ)) ((n : ℤ)*s) τ := by
  by_cases hb : (N : ℤ)∣r ∧ (N : ℤ)∣s
  · rw [TorsionDistributionTwo.reg_of_bad hb,imag_bad_sum n N hn hN τ r s hb]
  · exact reg_down_good n N hn hN τ r s hb

end ZInQ.Contrib.HeckePrimeRationality.ThetaRectangular
