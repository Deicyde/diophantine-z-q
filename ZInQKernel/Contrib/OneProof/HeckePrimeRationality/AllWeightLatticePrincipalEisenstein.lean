import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightGoodPrincipalEisenstein

/-!
# Actual lattice Eisenstein forms from finite residue decomposition

Absolute convergence at k>2 permits the genuine Euclidean residue-grid
bijection and finite summation of the congruence rows. Averaging only Good
rows yields the actual lattice G_k, including every even weight. Bad rows
are the actual lattice sum, not a zero convention; odd lattice sums vanish.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open Complex Filter Set ModularForm
open scoped Topology Real UpperHalfPlane Modular MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.AllWeightLatticeEisenstein

open ZInQ.Contrib.HeckePrimeRationality
open AllWeightGoodEisenstein TorsionInvariants TorsionInvariantForms TorsionWeightThree

/-- Euclidean residue and quotient enumerate every integer exactly once. -/
def residueEquiv (N : ℕ) (hN : 0 < N) : (Fin N × ℤ) ≃ ℤ where
  toFun p := (p.1 : ℕ) + (N : ℤ) * p.2
  invFun q := (⟨(q % (N : ℤ)).toNat, by
    have hpos : (0 : ℤ) < N := by exact_mod_cast hN
    have hn := Int.emod_nonneg q hpos.ne'
    have ht := Int.emod_lt_of_pos q hpos
    exact_mod_cast (by rw [Int.toNat_of_nonneg hn]; exact ht : ((q % (N : ℤ)).toNat : ℤ) < N)⟩,
    q / (N : ℤ))
  left_inv := by
    intro p
    apply Prod.ext
    · apply Fin.ext
      have hp0 : (0 : ℤ) ≤ (p.1 : ℕ) := by positivity
      have hplt : ((p.1 : ℕ) : ℤ) < N := by exact_mod_cast p.1.isLt
      simp only [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hp0 hplt, Int.toNat_natCast]
    · change ((((p.1 : ℕ) : ℤ) + (N : ℤ) * p.2) / (N : ℤ)) = p.2
      have hp0 : (0 : ℤ) ≤ (p.1 : ℕ) := by positivity
      have hplt : ((p.1 : ℕ) : ℤ) < N := by exact_mod_cast p.1.isLt
      rw [Int.add_mul_ediv_left _ _ (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0),
        Int.ediv_eq_zero_of_lt hp0 hplt, zero_add]
  right_inv := by
    intro q
    change ((q % (N : ℤ)).toNat : ℤ) + (N : ℤ) * (q / (N : ℤ)) = q
    have hNc : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [Int.toNat_of_nonneg (Int.emod_nonneg q hNc)]
    exact Int.emod_add_mul_ediv q (N : ℤ)

lemma residueEquiv_apply (N : ℕ) (hN : 0 < N) (p : Fin N × ℤ) :
    residueEquiv N hN p = ((p.1 : ℕ) : ℤ) + (N : ℤ) * p.2 := rfl

/-- The full genuine residue-grid bijection, without a summation assumption. -/
def residueGridEquiv (N : ℕ) (hN : 0 < N) : ((Fin N × Fin N) × (ℤ × ℤ)) ≃ (ℤ × ℤ) :=
  (Equiv.prodProdProdComm (Fin N) (Fin N) ℤ ℤ).trans
    (Equiv.prodCongr (residueEquiv N hN) (residueEquiv N hN))

lemma residueGridEquiv_apply (N : ℕ) (hN : 0 < N) (p : (Fin N × Fin N) × (ℤ × ℤ)) :
    residueGridEquiv N hN p =
      (((p.1.1 : ℕ) : ℤ) + N*p.2.1, ((p.1.2 : ℕ) : ℤ) + N*p.2.2) := rfl

/-- Absolute convergence justifies the complete finite residue decomposition. -/
theorem lattice_residue_sum (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    (∑ p : Fin N × Fin N, ∑' q : ℤ × ℤ, EisensteinSeries.eisSummand (k : ℤ)
      ![((p.1 : ℕ) : ℤ) + N*q.1, ((p.2 : ℕ) : ℤ) + N*q.2] τ) =
      (ThetaWeierstrass.periodPair τ).G k := by
  have hs := TorsionInvariantNormalizations.hasSum_actual_lattice_eisenstein τ k (by omega)
  have hg := (residueGridEquiv N hN).hasSum_iff.mpr hs
  have h := hg.summable.tsum_prod
  rw [hg.tsum_eq, tsum_fintype] at h
  simpa only [Function.comp_apply, residueGridEquiv_apply] using h.symm

/-- Actual scaling of every bad congruence row; no even bad row is set to zero. -/
lemma scaled_bad_term (N : ℕ) (hN : 0 < N) (k : ℕ) (m n : ℤ) (q : ℤ × ℤ) (τ : ℍ) :
    (N : ℂ) ^ k * EisensteinSeries.eisSummand (k : ℤ) ![N*m + N*q.1,N*n + N*q.2] τ =
      EisensteinSeries.eisSummand (k : ℤ) ![m+q.1,n+q.2] τ := by
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  simp only [EisensteinSeries.eisSummand, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, _root_.zpow_neg, _root_.zpow_natCast]
  push_cast
  rw [show (((N : ℂ) * (m : ℂ) + N*q.1) * (τ : ℂ) + (N*n + N*q.2)) =
      N * (((m : ℂ) + q.1) * (τ : ℂ) + (n + q.2)) by ring]
  rw [mul_pow, mul_inv_rev, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero k hNc), mul_one]

/-- Every actual bad congruence series is absolutely summable and equals the actual lattice value. -/
theorem bad_row_eq_lattice (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : 3 ≤ k)
    (a b : ℤ) (hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) (τ : ℍ) :
    (N : ℂ) ^ k * ∑' q : ℤ × ℤ, EisensteinSeries.eisSummand (k : ℤ) ![a+N*q.1,b+N*q.2] τ =
      (ThetaWeierstrass.periodPair τ).G k := by
  obtain ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩ := hb
  have hs := TorsionInvariantNormalizations.hasSum_actual_lattice_eisenstein τ k (by omega)
  have hg := (Equiv.addLeft (m,n)).hasSum_iff.mpr hs
  have he : (fun q : ℤ × ℤ => (N : ℂ) ^ k * EisensteinSeries.eisSummand (k : ℤ)
      ![N*m+N*q.1,N*n+N*q.2] τ) =
      (fun q : ℤ × ℤ => EisensteinSeries.eisSummand (k : ℤ) ![m+q.1,n+q.2] τ) :=
    funext fun q => scaled_bad_term N hN k m n q τ
  rw [← tsum_mul_left, he]
  change HasSum (fun q : ℤ × ℤ => EisensteinSeries.eisSummand (k : ℤ) ![m+q.1,n+q.2] τ)
    ((ThetaWeierstrass.periodPair τ).G k) at hg
  exact hg.tsum_eq

/-- The scaled zero row is the actual lattice series. -/
lemma zero_row_eq_lattice (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    (N : ℂ) ^ k * ∑' q : ℤ × ℤ, EisensteinSeries.eisSummand (k : ℤ)
      ![N*q.1,N*q.2] τ = (ThetaWeierstrass.periodPair τ).G k := by
  simpa only [zero_add] using bad_row_eq_lattice N hN k hk 0 0 ⟨dvd_zero _,dvd_zero _⟩ τ

/-- Removing only the zero row gives the factor N^k−1, by absolute finite residue decomposition. -/
theorem good_residue_sum (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    (∑ p ∈ nonzeroIndices N hN, (N : ℂ) ^ k * ∑' q : ℤ × ℤ,
      EisensteinSeries.eisSummand (k : ℤ) ![((p.1 : ℕ) : ℤ)+N*q.1,((p.2 : ℕ) : ℤ)+N*q.2] τ) =
      ((N : ℂ) ^ k - 1) * (ThetaWeierstrass.periodPair τ).G k := by
  have hs := lattice_residue_sum N hN k hk τ
  have hsum := congrArg (fun z : ℂ => (N : ℂ) ^ k * z) hs
  rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (WeierstrassDistributionNat.p0 N hN))] at hsum
  simp only [WeierstrassDistributionNat.p0, Nat.cast_zero, zero_add,
    zero_row_eq_lattice N hN k hk] at hsum
  change (ThetaWeierstrass.periodPair τ).G k + (∑ p ∈ nonzeroIndices N hN,
    (N : ℂ) ^ k * ∑' q : ℤ × ℤ, EisensteinSeries.eisSummand (k : ℤ)
      ![((p.1 : ℕ) : ℤ)+N*q.1,((p.2 : ℕ) : ℤ)+N*q.2] τ) =
      (N : ℂ) ^ k * (ThetaWeierstrass.periodPair τ).G k at hsum
  linear_combination hsum

lemma residue_average_denominator (N : ℕ) (hN : 2 ≤ N) (k : ℕ) (hk : 0 < k) : (N : ℂ) ^ k - 1 ≠ 0 := by
  have hn : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hp : (1 : ℝ) < (N : ℝ) ^ k := one_lt_pow₀ hn hk.ne'
  have he : (N : ℝ) ^ k - 1 ≠ 0 := by linarith
  exact_mod_cast he

/-- The actual lattice series bundle is constructed by averaging the already bound Good derivative forms. -/
def latticeEisensteinForm (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) : Weight N (k : ℤ) :=
  ((N : ℂ) ^ k - 1)⁻¹ • ∑ p ∈ nonzeroIndices N (by omega),
    ModularForm.mcast (congrArg (fun n : ℕ => (n : ℤ)) (by omega : k-2+2=k))
      (derivativeEisensteinForm N h3 (k-2) (p.1 : ℕ) (p.2 : ℕ))

/-- The averaged genuine form evaluates to the actual lattice G_k in every weight k≥3. -/
theorem latticeEisensteinForm_apply_actual (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    latticeEisensteinForm N h3 k hk τ = (ThetaWeierstrass.periodPair τ).G k := by
  have hpos : 0 < N := by omega
  have he : k-2+2=k := by omega
  have hterm (p : Fin N × Fin N) (hp : p ∈ nonzeroIndices N hpos) :
      derivativeEisensteinForm N h3 (k-2) (p.1 : ℕ) (p.2 : ℕ) τ =
      (N : ℂ) ^ k * ∑' q : ℤ × ℤ, EisensteinSeries.eisSummand (k : ℤ)
        ![((p.1 : ℕ) : ℤ)+N*q.1,((p.2 : ℕ) : ℤ)+N*q.2] τ := by
    have hg := (TorsionInvariantNormalizations.mem_nonzeroIndices_iff_good N hpos p).mp hp
    simpa only [he] using!
      derivativeEisensteinForm_apply_actual N h3 (k-2) (by omega) (p.1 : ℕ) (p.2 : ℕ) hg τ
  simp only [latticeEisensteinForm, _root_.smul_apply, _root_.sum_apply, ModularForm.mcast_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl hterm, good_residue_sum N hpos k hk τ]
  have hn := residue_average_denominator N (by omega) k (by omega)
  field_simp [hn]

/-- Actual lattice Eisenstein forms in every weight k≥3 lie in the same-level Good product span. -/
theorem latticeEisensteinForm_mem (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) :
    latticeEisensteinForm N h3 k hk ∈ homogeneousProductSpan N (by omega) k := by
  unfold latticeEisensteinForm
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro p _
  exact cast_homogeneous_mem N (by omega) _ _ (by omega) _
    (derivativeEisensteinForm_mem N h3 (k-2) (p.1 : ℕ) (p.2 : ℕ))

/-- Bad odd rows vanish for the actual lattice-negation reason. -/
theorem bad_row_odd_zero (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : 3 ≤ k) (hodd : Odd k)
    (a b : ℤ) (hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) (τ : ℍ) :
    (N : ℂ) ^ k * ∑' q : ℤ × ℤ, EisensteinSeries.eisSummand (k : ℤ) ![a+N*q.1,b+N*q.2] τ = 0 := by
  rw [bad_row_eq_lattice N hN k hk a b hb τ, PeriodPair.G_eq_zero_of_odd _ k hodd]

/-- All actual principal congruence rows, including even bad rows, have same-level product bundles. -/
theorem actual_all_label_principal_eisenstein_bundle (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a b : ℤ) : ∃ f : Weight N (k : ℤ), f ∈ homogeneousProductSpan N (by omega) k ∧
      ∀ τ : ℍ, f τ = (N : ℂ) ^ k * ∑' q : ℤ × ℤ,
        EisensteinSeries.eisSummand (k : ℤ) ![a+N*q.1,b+N*q.2] τ := by
  by_cases hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · refine ⟨latticeEisensteinForm N h3 k hk, latticeEisensteinForm_mem N h3 k hk, ?_⟩
    intro τ
    rw [latticeEisensteinForm_apply_actual, bad_row_eq_lattice N (by omega) k hk a b hb τ]
  · exact actual_good_principal_eisenstein_bundle N h3 k hk a b hb

end ZInQ.Contrib.HeckePrimeRationality.AllWeightLatticeEisenstein
