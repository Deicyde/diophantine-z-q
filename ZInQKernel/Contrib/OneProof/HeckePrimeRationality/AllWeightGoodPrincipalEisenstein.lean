import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightWeierstrassDifferentialExpressions

/-!
# All-weight actual Good-label principal Eisenstein series

The actual translated-congruence inverse-power series is bound to actual
ordinary WP derivatives and to the weighted expression recurrence. The
resulting forms lie in the same-level Good product span for every weight
at least three. No series function is replaced by its polynomial expression.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open Complex Filter Set ModularForm
open scoped Topology Real UpperHalfPlane Modular MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.AllWeightGoodEisenstein

open ZInQ.Contrib.HeckePrimeRationality
open WeierstrassDifferentialExpressions TorsionInvariantForms TorsionWeightThree

/-- Actual WP derivative coefficients from Mathlib's absolutely convergent power-series expansion. -/
theorem wp_derivative_sumInvPow (L : _root_.PeriodPair) (r : ℕ) (hr : 0 < r) {z : ℂ}
    (hz : z ∉ L.lattice) :
    iteratedDeriv r L.weierstrassP z = ((r + 1).factorial : ℂ) * L.sumInvPow z (r + 2) := by
  have h := L.iteratedDeriv_weierstrassPExcept_self z (n := r)
  rw [L.weierstrassPExcept_of_notMem z hz] at h
  simpa only [ite_eq_right hr.ne'] using h

/-- All ordinary WP derivatives retain the actual parity with its exact sign. -/
theorem wp_derivative_neg (L : _root_.PeriodPair) (r : ℕ) (z : ℂ) :
    iteratedDeriv r L.weierstrassP (-z) = (-1 : ℂ) ^ r * iteratedDeriv r L.weierstrassP z := by
  have he : (fun w : ℂ => L.weierstrassP (-w)) = L.weierstrassP := funext L.weierstrassP_neg
  have h := iteratedDeriv_comp_neg r L.weierstrassP (-z)
  rw [he, neg_neg] at h
  exact h

lemma derivative_factorial_ne_zero (r : ℕ) : ((r + 1).factorial : ℂ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)

/-- The actual shifted inverse-power grid sum has the ordinary WP derivative as its normalized value. -/
theorem hasSum_inversePower_good (τ : ℍ) (r : ℕ) (hr : 0 < r) {z : ℂ}
    (hz : z ∉ (ThetaWeierstrass.periodPair τ).lattice) :
    HasSum (fun p : ℤ × ℤ => 1 / (z + (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)) ^ (r + 2))
      (((-1 : ℂ) ^ r / ((r + 1).factorial : ℂ)) *
        iteratedDeriv r (ThetaWeierstrass.periodPair τ).weierstrassP z) := by
  let L := ThetaWeierstrass.periodPair τ
  have h := L.hasSum_sumInvPow (-z) (by omega : 2 < r + 2)
  have hnz : -z ∉ L.lattice := fun h => hz (by simpa using L.lattice.neg_mem h)
  have hd := wp_derivative_sumInvPow L r hr hnz
  rw [wp_derivative_neg] at hd
  have hs : L.sumInvPow (-z) (r + 2) =
      ((-1 : ℂ) ^ r / ((r + 1).factorial : ℂ)) * iteratedDeriv r L.weierstrassP z := by
    field_simp [derivative_factorial_ne_zero r]
    linear_combination -hd
  rw [hs] at h
  have hg := (EisensteinWeightTwo.gridEquiv τ).hasSum_iff.mpr h
  refine hg.congr_fun ?_
  intro p
  simp only [Function.comp_apply, EisensteinWeightTwo.gridEquiv_coe, sub_neg_eq_add, one_div]
  congr 2
  ring

/-- The congruence inverse-power term is the scaled actual shifted lattice term. -/
lemma inversePower_congruence (N : ℕ) (hN : 0 < N) (k : ℕ) (a b : ℤ) (τ : ℍ) (p : ℤ × ℤ) :
    1 / (CompletedTheta.torsionPoint N a b τ + (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ)) ^ k =
      (N : ℂ) ^ k * EisensteinSeries.eisSummand (k : ℤ) ![a + N * p.1, b + N * p.2] τ := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have heq : CompletedTheta.torsionPoint N a b τ + (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ) =
      ((((a + N * p.1 : ℤ) : ℂ) * (τ : ℂ) + ((b + N * p.2 : ℤ) : ℂ)) / (N : ℂ)) := by
    unfold CompletedTheta.torsionPoint
    push_cast
    field_simp
    ring
  rw [heq]
  simp only [EisensteinSeries.eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, _root_.zpow_neg, _root_.zpow_natCast, div_pow, one_div, inv_div]
  rfl

/-- A genuine weight-(r+2) form from the actual derivative expression, not a replacement series definition. -/
def derivativeEisensteinForm (N : ℕ) (h3 : 3 ≤ N) (r : ℕ) (a b : ℤ) : Weight N ((r + 2 : ℕ) : ℤ) :=
  ((-1 : ℂ) ^ r / ((r + 1).factorial : ℂ)) • (wpJet r).toForm N h3 a b

/-- Same-level Good product membership is proved independently by the expression recurrence. -/
theorem derivativeEisensteinForm_mem (N : ℕ) (h3 : 3 ≤ N) (r : ℕ) (a b : ℤ) :
    derivativeEisensteinForm N h3 r a b ∈ homogeneousProductSpan N (by omega) (r + 2) :=
  Submodule.smul_mem _ _ (Expr.toForm_mem (wpJet r) N h3 a b)

/-- Literal actual translated-congruence series value of the form on every Good label. -/
theorem derivativeEisensteinForm_apply_actual (N : ℕ) (h3 : 3 ≤ N) (r : ℕ) (hr : 0 < r)
    (a b : ℤ) (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) (τ : ℍ) :
    derivativeEisensteinForm N h3 r a b τ =
      (N : ℂ) ^ (r + 2) * ∑' p : ℤ × ℤ,
        EisensteinSeries.eisSummand ((r + 2 : ℕ) : ℤ) ![a + N * p.1, b + N * p.2] τ := by
  have hpos : 0 < N := by omega
  have hz : CompletedTheta.torsionPoint N a b τ ∉ (ThetaWeierstrass.periodPair τ).lattice := by
    apply (ThetaWeierstrass.H_zero_iff_mem_lattice τ _).not.mp
    exact CompletedTheta.H_torsion_ne_zero N hpos τ a b hg
  have hs := (hasSum_inversePower_good τ r hr hz).div_const ((N : ℂ) ^ (r + 2))
  have hNc : (N : ℂ) ^ (r + 2) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hpos.ne')
  have hS : HasSum (fun p : ℤ × ℤ => EisensteinSeries.eisSummand ((r + 2 : ℕ) : ℤ)
      ![a + N * p.1, b + N * p.2] τ)
      (((( -1 : ℂ) ^ r / ((r + 1).factorial : ℂ)) *
        iteratedDeriv r (ThetaWeierstrass.periodPair τ).weierstrassP
          (CompletedTheta.torsionPoint N a b τ)) / (N : ℂ) ^ (r + 2)) := by
    refine hs.congr_fun ?_
    intro p
    rw [inversePower_congruence N hpos]
    exact (mul_div_cancel_left₀ _ hNc).symm
  rw [hS.tsum_eq]
  simp only [derivativeEisensteinForm, _root_.smul_apply, smul_eq_mul,
    Expr.toForm_apply (wpJet r) N h3 a b hg τ, wpJet_eval _ r hz]
  field_simp [hNc]

/-- The actual Good-label congruence summands are absolutely summable at all weights at least three. -/
theorem congruence_summable_good (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : 3 ≤ k)
    (a b : ℤ) (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) (τ : ℍ) :
    Summable (fun p : ℤ × ℤ => EisensteinSeries.eisSummand (k : ℤ) ![a + N*p.1,b + N*p.2] τ) := by
  have hz : CompletedTheta.torsionPoint N a b τ ∉ (ThetaWeierstrass.periodPair τ).lattice := by
    apply (ThetaWeierstrass.H_zero_iff_mem_lattice τ _).not.mp
    exact CompletedTheta.H_torsion_ne_zero N hN τ a b hg
  have hk' : k - 2 + 2 = k := by omega
  have hs := (hasSum_inversePower_good τ (k - 2) (by omega) hz).div_const ((N : ℂ) ^ k)
  rw [hk'] at hs
  refine (hs.congr_fun ?_).summable
  intro p
  rw [inversePower_congruence N hN]
  have hc : (N : ℂ) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')
  exact (mul_div_cancel_left₀ _ hc).symm

/-- Transporting a natural-number grade preserves the actual homogeneous product span. -/
lemma cast_homogeneous_mem (N : ℕ) (hN : 0 < N) (k l : ℕ) (he : k = l)
    (f : Weight N (k : ℤ)) (hf : f ∈ homogeneousProductSpan N hN k) :
    ModularForm.mcast (congrArg (fun n : ℕ => (n : ℤ)) he) f ∈ homogeneousProductSpan N hN l := by
  subst l
  exact hf

/-- All Nat weights k≥3 have an actual Good-label principal Eisenstein bundle in the same-level product span. -/
theorem actual_good_principal_eisenstein_bundle (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a b : ℤ) (hg : ¬ ((N : ℤ) ∣ a ∧ (N : ℤ) ∣ b)) :
    ∃ f : Weight N (k : ℤ), f ∈ homogeneousProductSpan N (by omega) k ∧
      ∀ τ : ℍ, f τ = (N : ℂ) ^ k * ∑' p : ℤ × ℤ,
        EisensteinSeries.eisSummand (k : ℤ) ![a + N*p.1,b + N*p.2] τ := by
  have he : k - 2 + 2 = k := by omega
  let f := ModularForm.mcast (congrArg (fun n : ℕ => (n : ℤ)) he)
    (derivativeEisensteinForm N h3 (k - 2) a b)
  refine ⟨f, ?_, ?_⟩
  · exact cast_homogeneous_mem N (by omega) _ _ he _
      (derivativeEisensteinForm_mem N h3 (k - 2) a b)
  · intro τ
    simpa only [f, ModularForm.mcast_apply, he] using!
      derivativeEisensteinForm_apply_actual N h3 (k - 2) (by omega) a b hg τ

end ZInQ.Contrib.HeckePrimeRationality.AllWeightGoodEisenstein
