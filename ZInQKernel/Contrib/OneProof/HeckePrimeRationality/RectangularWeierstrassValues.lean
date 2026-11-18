import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.RectangularWeierstrassAnalytic

/-!
# Rectangular transport of actual zero-extended Weierstrass torsion values

The cyclic correction is a finite sum of actual nonzero torsion WP values,
with the origin handled by the established zero extension. Good labels use
the actual off-lattice analytic identity. Bad labels are proved separately
by representative periodicity, so no pole value is evaluated as regular.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000

open Complex Filter Set
open scoped Topology Real UpperHalfPlane MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.RectangularWeierstrassValues

open ZInQ.Contrib.HeckePrimeRationality
open CompletedTheta ThetaWeierstrass TorsionWeierstrassData
open RectangularThetaLattice RectangularWeierstrassAnalytic

/-- The actual finite real cyclic x correction, zero-extended only at the origin. -/
def cyclicRealValue (n N : ℕ) (τ : ℍ) : ℂ :=
  ∑ b : Fin n, xValue (n*N) 0 ((N : ℤ)*(b : ℕ)) τ

/-- The actual finite imaginary cyclic x correction. -/
def cyclicImagValue (n N : ℕ) (τ : ℍ) : ℂ :=
  ∑ a : Fin n, xValue (n*N) ((N : ℤ)*(a : ℕ)) 0 τ

lemma cyclic_good (n N : ℕ) (hn : 0 < n) (hN : 0 < N) {b : Fin n}
    (hb : b ≠ cyclicZero n hn) : ¬ (((n*N : ℕ) : ℤ) ∣ (N : ℤ)*(b : ℕ)) := by
  intro hd
  have hNI : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hd' : (n : ℤ) ∣ ((b : ℕ) : ℤ) := by
    have h := hd
    rw [Nat.cast_mul, mul_comm (n : ℤ) (N : ℤ)] at h
    exact (mul_dvd_mul_iff_left hNI).mp h
  have h0 : (b : ℕ)=0 := Nat.eq_zero_of_dvd_of_lt (by exact_mod_cast hd') b.isLt
  exact hb (Fin.ext h0)

lemma cyclic_real_term (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (b : Fin n)
    (hb : b ≠ cyclicZero n hn) :
    xValue (n*N) 0 ((N : ℤ)*(b : ℕ)) τ = (periodPair τ).weierstrassP (realShift n b) := by
  have hg : ¬ (((n*N : ℕ) : ℤ) ∣ (0 : ℤ) ∧ ((n*N : ℕ) : ℤ) ∣ (N : ℤ)*(b : ℕ)) :=
    fun h => cyclic_good n N hn hN hb h.2
  rw [xValue_of_good _ _ _ _ hg]
  congr 1
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [torsionPoint, realShift]
  push_cast
  field_simp
  ring

lemma cyclic_imag_term (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (a : Fin n)
    (ha : a ≠ cyclicZero n hn) :
    xValue (n*N) ((N : ℤ)*(a : ℕ)) 0 τ = (periodPair τ).weierstrassP (imagShift n τ a) := by
  have hg : ¬ (((n*N : ℕ) : ℤ) ∣ (N : ℤ)*(a : ℕ) ∧ ((n*N : ℕ) : ℤ) ∣ (0 : ℤ)) :=
    fun h => cyclic_good n N hn hN ha h.1
  rw [xValue_of_good _ _ _ _ hg]
  congr 1
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [torsionPoint, imagShift]
  push_cast
  field_simp
  ring

/-- The actual real cyclic sum has the derived finite-part normalization, independent of N. -/
theorem cyclicRealValue_eq_finitePart (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) :
    cyclicRealValue n N τ = (n : ℂ)*finitePart τ - (n : ℂ)^2*finitePart (upTau n hn τ) := by
  unfold cyclicRealValue
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (cyclicZero n hn))]
  simp only [cyclicZero, Nat.cast_zero, mul_zero, xValue_zero, zero_add]
  rw [← real_cyclic_finitePart n hn τ]
  exact Finset.sum_congr rfl fun b hb => cyclic_real_term n N hn hN τ b (Finset.ne_of_mem_erase hb)

/-- The actual imaginary cyclic sum has the derived finite-part normalization. -/
theorem cyclicImagValue_eq_finitePart (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) :
    cyclicImagValue n N τ = (n : ℂ)*finitePart τ - finitePart (downTau n hn τ) := by
  unfold cyclicImagValue
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (cyclicZero n hn))]
  simp only [cyclicZero, Nat.cast_zero, mul_zero, xValue_zero, zero_add]
  rw [← imag_cyclic_finitePart n hn τ]
  exact Finset.sum_congr rfl fun a ha => cyclic_imag_term n N hn hN τ a (Finset.ne_of_mem_erase ha)

/-- Imaginary rectangular preimages are the actual torsion coordinates. -/
lemma imag_torsion_point (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (τ : ℍ) (r s : ℤ) (a : Fin n) :
    torsionPoint (n*N) (r+(N : ℤ)*(a : ℕ)) ((n : ℤ)*s) τ =
      torsionPoint N r s (downTau n hn τ) + imagShift n τ a := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [torsionPoint,imagShift,downTau_coe]
  push_cast
  field_simp
  ring

/-- Actual real rectangular x transport on Good source labels. -/
theorem xValue_up_good (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (r s : ℤ)
    (hg : ¬ ((N : ℤ) ∣ r ∧ (N : ℤ) ∣ s)) (τ : ℍ) :
    xValue N r s (upTau n hn τ) = (1/(n : ℂ)^2) *
      ((∑ b : Fin n, xValue (n*N) ((n : ℤ)*r) (s+(N : ℤ)*(b : ℕ)) τ) - cyclicRealValue n N τ) := by
  let z := torsionPoint N r s (upTau n hn τ)/(n : ℂ)
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hz : (n : ℂ)*z = torsionPoint N r s (upTau n hn τ) := by dsimp [z]; field_simp
  have hs : ∀ b : Fin n, z+realShift n b ∉ (periodPair τ).lattice := by
    intro b
    rw [show z+realShift n b = torsionPoint (n*N) ((n : ℤ)*r) (s+(N : ℤ)*(b : ℕ)) τ from
      (ThetaRectangular.real_torsion_point n N hn hN τ r s b).symm]
    exact WeierstrassForms.tp_notMem (Nat.mul_pos hn hN) (ThetaRectangular.good_real_lift hn hg b) τ
  have ht : (n : ℂ)*z ∉ (periodPair (upTau n hn τ)).lattice := by
    rw [hz]
    exact WeierstrassForms.tp_notMem hN hg _
  have hw := wp_real_with_finitePart n hn τ hs ht
  rw [hz] at hw
  have hc := cyclicRealValue_eq_finitePart n N hn hN τ
  have hterm (b : Fin n) : xValue (n*N) ((n : ℤ)*r) (s+(N : ℤ)*(b : ℕ)) τ =
      (periodPair τ).weierstrassP (z+realShift n b) := by
    rw [xValue_of_good _ _ _ _ (ThetaRectangular.good_real_lift hn hg b),ThetaRectangular.real_torsion_point n N hn hN]
    rfl
  rw [xValue_of_good _ _ _ _ hg]
  simp only [hterm]
  field_simp
  linear_combination hw + hc

/-- Actual imaginary rectangular x transport on Good source labels. -/
theorem xValue_down_good (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (r s : ℤ)
    (hg : ¬ ((N : ℤ) ∣ r ∧ (N : ℤ) ∣ s)) (τ : ℍ) :
    xValue N r s (downTau n hn τ) =
      (∑ a : Fin n, xValue (n*N) (r+(N : ℤ)*(a : ℕ)) ((n : ℤ)*s) τ) - cyclicImagValue n N τ := by
  let z := torsionPoint N r s (downTau n hn τ)
  have hs : ∀ a : Fin n,z+imagShift n τ a ∉ (periodPair τ).lattice := by
    intro a
    rw [show z+imagShift n τ a = torsionPoint (n*N) (r+(N : ℤ)*(a : ℕ)) ((n : ℤ)*s) τ from
      (imag_torsion_point n N hn hN τ r s a).symm]
    exact WeierstrassForms.tp_notMem (Nat.mul_pos hn hN) (ThetaRectangular.good_imag_lift hn hg a) τ
  have ht : z ∉ (periodPair (downTau n hn τ)).lattice := WeierstrassForms.tp_notMem hN hg _
  have hw := wp_imag_with_finitePart n hn τ hs ht
  have hc := cyclicImagValue_eq_finitePart n N hn hN τ
  rw [xValue_of_good _ _ _ _ hg]
  have hterm (a : Fin n) : xValue (n*N) (r+(N : ℤ)*(a : ℕ)) ((n : ℤ)*s) τ =
      (periodPair τ).weierstrassP (z+imagShift n τ a) := by
    rw [xValue_of_good _ _ _ _ (ThetaRectangular.good_imag_lift hn hg a),imag_torsion_point n N hn hN]
  simp only [hterm]
  linear_combination hw + hc

/-- The real shifted x-sum on a bad source label is the actual cyclic correction, not zero. -/
theorem real_bad_sum (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (r s : ℤ)
    (hb : (N : ℤ) ∣ r ∧ (N : ℤ) ∣ s) (τ : ℍ) :
    (∑ b : Fin n, xValue (n*N) ((n : ℤ)*r) (s+(N : ℤ)*(b : ℕ)) τ) = cyclicRealValue n N τ := by
  obtain ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩ := hb
  let g : ℤ → ℂ := fun k => xValue (n*N) 0 ((N : ℤ)*k) τ
  have hp (k : ℤ) : g (k+n)=g k := by
    have h := WeierstrassDistributionNat.xValue_shift (Nat.mul_pos hn hN) 0 ((N : ℤ)*k) 0 1 τ
    simpa only [g,Nat.cast_mul,mul_zero,mul_one,mul_add,zero_add,add_mul,mul_comm] using h
  have ht (b : Fin n) : xValue (n*N) ((n : ℤ)*((N : ℤ)*u)) ((N : ℤ)*v+(N : ℤ)*(b : ℕ)) τ =
      g ((b : ℤ)+v) := by
    rw [show (n : ℤ)*((N : ℤ)*u)=0+((n*N : ℕ) : ℤ)*u by push_cast;ring,
      show (N : ℤ)*v+(N : ℤ)*(b : ℕ)=(N : ℤ)*((b : ℤ)+v)+((n*N : ℕ) : ℤ)*0 by ring,
      WeierstrassDistributionNat.xValue_shift (Nat.mul_pos hn hN)]
  simp_rw [ht]
  rw [Fin.sum_univ_eq_sum_range (fun b : ℕ => g ((b : ℤ)+v)) n,
    AllLevelAverage.sum_range_shift g hp v]
  exact (Fin.sum_univ_eq_sum_range (fun b : ℕ => g (b : ℤ)) n).symm

/-- The imaginary shifted x-sum on a bad source label has its separately proved cyclic value. -/
theorem imag_bad_sum (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (r s : ℤ)
    (hb : (N : ℤ) ∣ r ∧ (N : ℤ) ∣ s) (τ : ℍ) :
    (∑ a : Fin n, xValue (n*N) (r+(N : ℤ)*(a : ℕ)) ((n : ℤ)*s) τ) = cyclicImagValue n N τ := by
  obtain ⟨⟨u,rfl⟩,⟨v,rfl⟩⟩ := hb
  let g : ℤ → ℂ := fun k => xValue (n*N) ((N : ℤ)*k) 0 τ
  have hp (k : ℤ) : g (k+n)=g k := by
    have h := WeierstrassDistributionNat.xValue_shift (Nat.mul_pos hn hN) ((N : ℤ)*k) 0 1 0 τ
    simpa only [g,Nat.cast_mul,mul_zero,mul_one,mul_add,zero_add,add_mul,mul_comm] using h
  have ht (a : Fin n) : xValue (n*N) ((N : ℤ)*u+(N : ℤ)*(a : ℕ)) ((n : ℤ)*((N : ℤ)*v)) τ =
      g ((a : ℤ)+u) := by
    rw [show (N : ℤ)*u+(N : ℤ)*(a : ℕ)=(N : ℤ)*((a : ℤ)+u)+((n*N : ℕ) : ℤ)*0 by ring,
      show (n : ℤ)*((N : ℤ)*v)=0+((n*N : ℕ) : ℤ)*v by push_cast;ring,
      WeierstrassDistributionNat.xValue_shift (Nat.mul_pos hn hN)]
  simp_rw [ht]
  rw [Fin.sum_univ_eq_sum_range (fun a : ℕ => g ((a : ℤ)+u)) n,
    AllLevelAverage.sum_range_shift g hp u]
  exact (Fin.sum_univ_eq_sum_range (fun a : ℕ => g (a : ℤ)) n).symm

/-- All-label actual real rectangular transport, including n=1 and every positive original level. -/
theorem xValue_up (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (r s : ℤ) (τ : ℍ) :
    xValue N r s (upTau n hn τ) = (1/(n : ℂ)^2) *
      ((∑ b : Fin n,xValue (n*N) ((n : ℤ)*r) (s+(N : ℤ)*(b : ℕ)) τ) - cyclicRealValue n N τ) := by
  by_cases hb : (N : ℤ) ∣ r ∧ (N : ℤ) ∣ s
  · rw [WeierstrassForms.xValue_bad hb,real_bad_sum n N hn hN r s hb τ,sub_self,mul_zero]
  · exact xValue_up_good n N hn hN r s hb τ

/-- All-label actual imaginary rectangular transport with the finite cyclic correction. -/
theorem xValue_down (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (r s : ℤ) (τ : ℍ) :
    xValue N r s (downTau n hn τ) =
      (∑ a : Fin n,xValue (n*N) (r+(N : ℤ)*(a : ℕ)) ((n : ℤ)*s) τ) - cyclicImagValue n N τ := by
  by_cases hb : (N : ℤ) ∣ r ∧ (N : ℤ) ∣ s
  · rw [WeierstrassForms.xValue_bad hb,imag_bad_sum n N hn hN r s hb τ,sub_self]
  · exact xValue_down_good n N hn hN r s hb τ

/-- The actual completed weight-one normalization inherits the all-label real rectangular identity. -/
theorem lambdaValue_up (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (r s : ℤ) (τ : ℍ) :
    lambdaValue N r s (upTau n hn τ) = (1/(n : ℂ)) *
      ∑ b : Fin n,lambdaValue (n*N) ((n : ℤ)*r) (s+(N : ℤ)*(b : ℕ)) τ := by
  rw [lambdaValue,ThetaRectangular.reg_up n N hn hN τ r s]
  simp only [lambdaValue]
  rw [← Finset.mul_sum]
  ring

/-- The imaginary completed weight-one identity keeps the established zero extension. -/
theorem lambdaValue_down (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (r s : ℤ) (τ : ℍ) :
    lambdaValue N r s (downTau n hn τ) =
      ∑ a : Fin n,lambdaValue (n*N) (r+(N : ℤ)*(a : ℕ)) ((n : ℤ)*s) τ := by
  rw [lambdaValue,ThetaRectangular.reg_down n N hn hN τ r s]
  simp only [lambdaValue,Finset.mul_sum]

end ZInQ.Contrib.HeckePrimeRationality.RectangularWeierstrassValues
