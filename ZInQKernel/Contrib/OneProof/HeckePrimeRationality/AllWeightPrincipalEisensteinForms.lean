import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightLatticePrincipalEisenstein

/-!
# All-label actual principal Eisenstein forms in every weight at least three

A Good row is realized by the actual weighted WP-derivative expression.
A bad row is realized by the actual lattice Eisenstein average, so even
bad rows are retained rather than set to zero. All congruence series are
proved absolutely summable before the literal actual-object identification.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open Complex Filter Set ModularForm
open scoped Topology Real UpperHalfPlane Modular MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.AllWeightPrincipalEisensteinForms

open ZInQ.Contrib.HeckePrimeRationality
open AllWeightGoodEisenstein AllWeightLatticeEisenstein TorsionInvariantForms TorsionWeightThree

/-- Explicit absolute convergence for actual bad rows by the proved scaled lattice reindexing. -/
theorem congruence_summable_bad (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : 3 ≤ k)
    (a b : ℤ) (hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) (τ : ℍ) :
    Summable (fun q : ℤ × ℤ => EisensteinSeries.eisSummand (k : ℤ) ![a+N*q.1,b+N*q.2] τ) := by
  obtain ⟨⟨m, rfl⟩, ⟨n, rfl⟩⟩ := hb
  have hs := TorsionInvariantNormalizations.hasSum_actual_lattice_eisenstein τ k (by omega)
  have hg := (Equiv.addLeft (m,n)).hasSum_iff.mpr hs
  change HasSum (fun q : ℤ × ℤ => EisensteinSeries.eisSummand (k : ℤ) ![m+q.1,n+q.2] τ)
    ((ThetaWeierstrass.periodPair τ).G k) at hg
  have hc : (N : ℂ) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hN.ne')
  refine ((hg.div_const ((N : ℂ) ^ k)).congr_fun ?_).summable
  intro q
  have he := scaled_bad_term N hN k m n q τ
  apply (eq_div_iff hc).mpr
  linear_combination he

/-- Absolute convergence at every integer label, with no Good or primitive restriction. -/
theorem congruence_summable_all (N : ℕ) (hN : 0 < N) (k : ℕ) (hk : 3 ≤ k) (a b : ℤ) (τ : ℍ) :
    Summable (fun q : ℤ × ℤ => EisensteinSeries.eisSummand (k : ℤ) ![a+N*q.1,b+N*q.2] τ) := by
  by_cases hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b
  · exact congruence_summable_bad N hN k hk a b hb τ
  · exact congruence_summable_good N hN k hk a b hb τ

/-- The genuine all-label form; bad even rows use the actual nonzero lattice-series bundle. -/
def principalEisensteinForm (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) (a b : ℤ) : Weight N (k : ℤ) :=
  if (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b then latticeEisensteinForm N h3 k hk else
    ModularForm.mcast (congrArg (fun n : ℕ => (n : ℤ)) (by omega : k-2+2=k))
      (derivativeEisensteinForm N h3 (k-2) a b)

/-- Every all-label form is in the actual Good homogeneous product span at exactly the same level. -/
theorem principalEisensteinForm_mem (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k) (a b : ℤ) :
    principalEisensteinForm N h3 k hk a b ∈ homogeneousProductSpan N (by omega) k := by
  unfold principalEisensteinForm
  split_ifs with hb
  · exact latticeEisensteinForm_mem N h3 k hk
  · exact cast_homogeneous_mem N (by omega) _ _ (by omega) _ (derivativeEisensteinForm_mem N h3 (k-2) a b)

/-- Literal identification with the actual translated-congruence Mathlib inverse-power series. -/
theorem principalEisensteinForm_apply_actual (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a b : ℤ) (τ : ℍ) :
    principalEisensteinForm N h3 k hk a b τ = (N : ℂ) ^ k * ∑' q : ℤ × ℤ,
      EisensteinSeries.eisSummand (k : ℤ) ![a+N*q.1,b+N*q.2] τ := by
  unfold principalEisensteinForm
  split_ifs with hb
  · rw [latticeEisensteinForm_apply_actual, bad_row_eq_lattice N (by omega) k hk a b hb τ]
  · have he : k-2+2=k := by omega
    rw [ModularForm.mcast_apply]
    simpa only [he] using! derivativeEisensteinForm_apply_actual N h3 (k-2) (by omega) a b hb τ

/-- Bad rows evaluate to actual G_k, without an even-row zero convention. -/
theorem principalEisensteinForm_bad_apply (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (a b : ℤ) (hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) (τ : ℍ) :
    principalEisensteinForm N h3 k hk a b τ = (ThetaWeierstrass.periodPair τ).G k := by
  rw [principalEisensteinForm_apply_actual, bad_row_eq_lattice N (by omega) k hk a b hb τ]

/-- Bad odd forms vanish by actual lattice negation, not by the definition of the series. -/
theorem principalEisensteinForm_bad_odd_zero (N : ℕ) (h3 : 3 ≤ N) (k : ℕ) (hk : 3 ≤ k)
    (hodd : Odd k) (a b : ℤ) (hb : (N : ℤ) ∣ a ∧ (N : ℤ) ∣ b) :
    principalEisensteinForm N h3 k hk a b = 0 := by
  apply DFunLike.ext
  intro τ
  change principalEisensteinForm N h3 k hk a b τ = 0
  rw [principalEisensteinForm_bad_apply N h3 k hk a b hb τ, PeriodPair.G_eq_zero_of_odd _ k hodd]

/-- The zero row at weight four is the actual G₄ form, not zero. -/
theorem principalEisensteinForm_zero_four (N : ℕ) (h3 : 3 ≤ N) :
    principalEisensteinForm N h3 4 (by omega) 0 0 = TorsionInvariantForms.latticeG4Form N (by omega) := by
  apply DFunLike.ext
  intro τ
  rw [principalEisensteinForm_bad_apply N h3 4 (by omega) 0 0 ⟨dvd_zero _,dvd_zero _⟩ τ,
    TorsionInvariantForms.latticeG4Form_apply]

/-- The zero row at weight six is the actual G₆ form, not zero. -/
theorem principalEisensteinForm_zero_six (N : ℕ) (h3 : 3 ≤ N) :
    principalEisensteinForm N h3 6 (by omega) 0 0 = TorsionInvariantForms.latticeG6Form N (by omega) := by
  apply DFunLike.ext
  intro τ
  rw [principalEisensteinForm_bad_apply N h3 6 (by omega) 0 0 ⟨dvd_zero _,dvd_zero _⟩ τ,
    TorsionInvariantForms.latticeG6Form_apply]

end ZInQ.Contrib.HeckePrimeRationality.AllWeightPrincipalEisensteinForms
