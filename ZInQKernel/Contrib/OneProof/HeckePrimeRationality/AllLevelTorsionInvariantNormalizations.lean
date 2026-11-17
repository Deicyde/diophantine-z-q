import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionInvariantForms

/-!
# Actual nonzero torsion indices and lattice Eisenstein normalizations

The finite indices are in bijection with the nonzero ambient residue
classes, and each such index is a genuine good torsion point. The lattice
Eisenstein sums retain Mathlib's inverse-power definitions, with absolute
summability at weights four and six.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open Complex Filter
open scoped Topology Real UpperHalfPlane Modular MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionInvariantNormalizations

open ZInQ.Contrib.HeckePrimeRationality
open TorsionInvariants TorsionInvariantForms

/-- The complete finite label equivalence at the actual ambient level. -/
def indexLabelEquiv (N : ℕ) (hN : 0 < N) : (Fin N × Fin N) ≃ TorsionCorrelation.Point N := by
  let _ : NeZero N := ⟨hN.ne'⟩
  exact Equiv.prodCongr (ZMod.finEquiv N).toEquiv (ZMod.finEquiv N).toEquiv

lemma indexLabelEquiv_apply (N : ℕ) (hN : 0 < N) (p : Fin N × Fin N) :
    indexLabelEquiv N hN p = TorsionCorrelation.label N (p.1 : ℕ) (p.2 : ℕ) := by
  cases N with
  | zero => omega
  | succ n =>
    apply Prod.ext
    · simpa only [indexLabelEquiv, Equiv.prodCongr_apply, TorsionCorrelation.label,
        Int.cast_natCast, ZMod.finEquiv, ZMod.val] using!
        (ZMod.natCast_zmod_val (show ZMod (n + 1) from p.1)).symm
    · simpa only [indexLabelEquiv, Equiv.prodCongr_apply, TorsionCorrelation.label,
        Int.cast_natCast, ZMod.finEquiv, ZMod.val] using!
        (ZMod.natCast_zmod_val (show ZMod (n + 1) from p.2)).symm

lemma indexLabelEquiv_zero (N : ℕ) (hN : 0 < N) :
    indexLabelEquiv N hN (WeierstrassDistributionNat.p0 N hN) = 0 := by
  rw [indexLabelEquiv_apply]
  simp [WeierstrassDistributionNat.p0, TorsionCorrelation.label]

/-- The nonzero index finset is exactly the set of good finite torsion labels. -/
lemma mem_nonzeroIndices_iff_good (N : ℕ) (hN : 0 < N) (p : Fin N × Fin N) :
    p ∈ nonzeroIndices N hN ↔
      ¬ ((N : ℤ) ∣ ((p.1 : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((p.2 : ℕ) : ℤ)) := by
  let _ : NeZero N := ⟨hN.ne'⟩
  rw [TorsionFourierComparison.finite_good_iff]
  simp only [nonzeroIndices, Finset.mem_erase, Finset.mem_univ, and_true]
  have hp0 : p = WeierstrassDistributionNat.p0 N hN ↔ p.1 = 0 ∧ p.2 = 0 := by
    simp [WeierstrassDistributionNat.p0, Prod.ext_iff]
  have hn := not_congr hp0
  tauto

/-- Restricting the actual label equivalence gives the genuine nonzero-class bijection. -/
def nonzeroLabelEquiv (N : ℕ) (hN : 0 < N) :
    {p : Fin N × Fin N // p ∈ nonzeroIndices N hN} ≃ {P : TorsionCorrelation.Point N // P ≠ 0} :=
  (indexLabelEquiv N hN).subtypeEquiv (fun p => by
    simp only [nonzeroIndices, Finset.mem_erase, Finset.mem_univ, and_true]
    have he : indexLabelEquiv N hN p = 0 ↔ p = WeierstrassDistributionNat.p0 N hN := by
      rw [← indexLabelEquiv_zero N hN]
      exact (indexLabelEquiv N hN).injective.eq_iff
    exact not_congr he.symm)

/-- The actual count N²−1 is the count of nonzero ambient classes, not a cubic assertion at zero. -/
theorem card_nonzeroClasses (N : ℕ) (hN : 0 < N) :
    Nat.card {P : TorsionCorrelation.Point N // P ≠ 0} = N ^ 2 - 1 := by
  classical
  let _ : NeZero N := ⟨hN.ne'⟩
  rw [← Nat.card_congr (nonzeroLabelEquiv N hN), Nat.card_eq_fintype_card,
    Fintype.card_coe, card_nonzeroIndices]

/-- The actual lattice inverse-power sum is an absolutely convergent grid Eisenstein sum when k>2. -/
theorem hasSum_actual_lattice_eisenstein (τ : ℍ) (k : ℕ) (hk : 2 < k) :
    HasSum (fun p : ℤ × ℤ => EisensteinSeries.eisSummand (k : ℤ) ![p.1, p.2] τ)
      ((ThetaWeierstrass.periodPair τ).G k) := by
  have h := (ThetaWeierstrass.periodPair τ).hasSum_sumInvPow 0 hk
  rw [PeriodPair.sumInvPow_zero] at h
  have hg := (EisensteinWeightTwo.gridEquiv τ).hasSum_iff.mpr h
  refine hg.congr_fun ?_
  intro p
  simp only [Function.comp_apply, EisensteinWeightTwo.gridEquiv_coe, sub_zero,
    EisensteinSeries.eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    _root_.zpow_neg, _root_.zpow_natCast]

/-- Actual g₂ is 60 times the actual convergent weight-four lattice sum. -/
theorem g2_eq_actual_eisenstein_four (τ : ℍ) :
    (ThetaWeierstrass.periodPair τ).g₂ =
      (60 : ℂ) * ∑' p : ℤ × ℤ, EisensteinSeries.eisSummand 4 ![p.1, p.2] τ := by
  have hs := (hasSum_actual_lattice_eisenstein τ 4 (by norm_num)).tsum_eq
  norm_num only [Nat.cast_ofNat] at hs
  rw [hs, PeriodPair.g₂]

/-- Actual g₃ is 140 times the actual convergent weight-six lattice sum. -/
theorem g3_eq_actual_eisenstein_six (τ : ℍ) :
    (ThetaWeierstrass.periodPair τ).g₃ =
      (140 : ℂ) * ∑' p : ℤ × ℤ, EisensteinSeries.eisSummand 6 ![p.1, p.2] τ := by
  have hs := (hasSum_actual_lattice_eisenstein τ 6 (by norm_num)).tsum_eq
  norm_num only [Nat.cast_ofNat] at hs
  rw [hs, PeriodPair.g₃]

/-- The genuine weight-four invariant form evaluates to the actual G₄ lattice Eisenstein series. -/
theorem latticeG4Form_eq_actual_eisenstein (N : ℕ) (h2 : 2 ≤ N) (τ : ℍ) :
    latticeG4Form N h2 τ = ∑' p : ℤ × ℤ, EisensteinSeries.eisSummand 4 ![p.1, p.2] τ := by
  rw [latticeG4Form_apply]
  have hs := (hasSum_actual_lattice_eisenstein τ 4 (by norm_num)).tsum_eq
  norm_num only [Nat.cast_ofNat] at hs
  exact hs.symm

/-- The genuine weight-six invariant form evaluates to the actual G₆ lattice Eisenstein series. -/
theorem latticeG6Form_eq_actual_eisenstein (N : ℕ) (h2 : 2 ≤ N) (τ : ℍ) :
    latticeG6Form N h2 τ = ∑' p : ℤ × ℤ, EisensteinSeries.eisSummand 6 ![p.1, p.2] τ := by
  rw [latticeG6Form_apply]
  have hs := (hasSum_actual_lattice_eisenstein τ 6 (by norm_num)).tsum_eq
  norm_num only [Nat.cast_ofNat] at hs
  exact hs.symm

end ZInQ.Contrib.HeckePrimeRationality.TorsionInvariantNormalizations
