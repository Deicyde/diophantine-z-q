import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionCoefficients
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionForms
import ZInQKernel.Contrib.TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Basic
import ZInQKernel.Contrib.TauCeti.NumberTheory.ModularForms.Parity

/-!
# Zero-label obstruction to unregularized torsion distribution

The raw total quotient at the zero torsion label has value one half, rather
than the zero value used in finite Eisenstein distribution identities.
The nonzero two-torsion labels vanish. Thus the naive two-division identity
at the zero point is false, uniformly in the ambient positive level.
No weight-two trace closure is asserted here.
-/

noncomputable section

open Complex UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm
open ZInQ.Contrib.HeckePrimeRationality.Torsion

namespace ZInQ.Contrib.HeckePrimeRationality.AllLevelTraceTwoZeroConvention

/-- The actual shifted theta denominator vanishes at the zero row. -/
lemma theta_zero_row (N : ℕ) [NeZero N] (τ : ℍ) :
    jacobiTheta₂ (shiftedPoint N 0 0 τ) τ = 0 := by
  have h := ZInQ.Contrib.HeckePrimeRationality.AllLevelTorsionCoefficients.P_hasSum N 0 τ
  have hP : ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsionCoefficients.P (w N 0) = 0 := by
    ext m
    simp [ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsionCoefficients.P,
      ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsionCoefficients.triangularCoeff,
      ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsionCoefficients.pPair, w]
  rw [hP] at h
  simpa using h.tsum_eq.symm

/-- Total division gives a nonzero junk value at the excluded zero row. -/
lemma raw_zero_row (N : ℕ) [NeZero N] (τ : ℍ) :
    torsionLogDerivative N 0 0 τ = (1 / 2 : ℂ) := by
  simp [torsionLogDerivative, theta_zero_row N τ]

lemma good_neg (N : ℕ) {a b : ℤ}
    (h : ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.Good N (a, b)) :
    ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.Good N (-a, -b) := by
  simpa [ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.Good] using h

/-- The actual nonzero torsion family is odd in its row label. -/
lemma raw_neg (N : ℕ) (hN : 0 < N) (a b : ℤ)
    (h : ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.Good N (a, b)) (τ : ℍ) :
    torsionLogDerivative N (-a) (-b) τ = -torsionLogDerivative N a b τ := by
  have hslash := ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.F_slash hN
    (-1 : SL(2, ℤ)) (a, b) h
  have hact : ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsion.act (a, b)
      (-1 : SL(2, ℤ)) = (-a, -b) := by
    dsimp [ZInQ.Contrib.HeckePrimeRationality.ThetaFiveTorsion.act]
    simp
  rw [hact, ModularForm.SL_slash] at hslash
  change ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.F N (a, b) ∣[(1 : ℤ)]
    (mapGL ℝ (-1 : SL(2, ℤ))) =
      ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.F N (-a, -b) at hslash
  rw [Matrix.SpecialLinearGroup.mapGL_neg_one, ModularForm.slash_neg_one] at hslash
  have h' := congrFun hslash τ
  simpa [ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.F] using h'.symm

/-- Every admissible two-torsion row vanishes, including in an arbitrary ambient level. -/
lemma half_order_zero (N : ℕ) [NeZero N] (a b : ℤ)
    (h : ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.Good (2 * N) (a, b))
    (ha : (2 * N : ℤ) ∣ 2 * a) (hb : (2 * N : ℤ) ∣ 2 * b) (τ : ℍ) :
    torsionLogDerivative (2 * N) a b τ = 0 := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  have hN : 0 < N := NeZero.pos N
  have hs := ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.F_shift
    (show 0 < 2 * N by omega) h (-m) (-n) τ
  have hna : a + (2 * N : ℤ) * (-m) = -a := by linear_combination hm
  have hnb : b + (2 * N : ℤ) * (-n) = -b := by linear_combination hn
  push_cast at hs
  simp only [ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.F, hna, hnb] at hs
  rw [raw_neg (2 * N) (by omega) a b h τ] at hs
  linear_combination -hs / 2

/-- The naive two-division sum at the zero point has value one half, not twice that value. -/
theorem naive_two_division_counterexample (N : ℕ) [NeZero N] (τ : ℍ) :
    torsionLogDerivative (2 * N) 0 0 τ +
      torsionLogDerivative (2 * N) N 0 τ +
      torsionLogDerivative (2 * N) 0 N τ +
      torsionLogDerivative (2 * N) N N τ ≠
        (2 : ℂ) * torsionLogDerivative N 0 0 τ := by
  have hN : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
  have hn : ¬ (2 * N : ℤ) ∣ (N : ℤ) := by
    intro h
    exact (Int.le_of_dvd hN h).not_gt (by omega)
  have h10 : ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.Good (2 * N) ((N : ℤ), 0) := by
    exact fun h => hn h.1
  have h01 : ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.Good (2 * N) (0, (N : ℤ)) := by
    exact fun h => hn h.2
  have h11 : ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.Good (2 * N) ((N : ℤ), (N : ℤ)) := by
    exact fun h => hn h.1
  rw [half_order_zero N N 0 h10 (by exact ⟨1, by ring⟩) (dvd_zero _) τ,
    half_order_zero N 0 N h01 (dvd_zero _) (by exact ⟨1, by ring⟩) τ,
    half_order_zero N N N h11 (by exact ⟨1, by ring⟩) (by exact ⟨1, by ring⟩) τ,
    raw_zero_row (2 * N) τ, raw_zero_row N τ]
  norm_num

/-- The first lattice translate of the raw zero label has the different junk value three halves. -/
lemma raw_lattice_row (N : ℕ) [NeZero N] (τ : ℍ) :
    torsionLogDerivative N N 0 τ = (3 / 2 : ℂ) := by
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hz : shiftedPoint N N 0 τ = shiftedPoint N 0 0 τ + (τ : ℂ) := by
    dsimp [shiftedPoint]
    push_cast
    field_simp [hN0]
    ring
  have htheta : jacobiTheta₂ (shiftedPoint N N 0 τ) τ = 0 := by
    rw [hz, jacobiTheta₂_add_left', theta_zero_row N τ, mul_zero]
  simp [torsionLogDerivative, htheta, hN0]
  norm_num

/-- Even a nonzero preimage is insufficient for raw distribution when its double is the zero point. -/
theorem naive_two_division_good_preimage_failure (N : ℕ) [NeZero N] (τ : ℍ) :
    torsionLogDerivative (2 * N) N 0 τ +
      torsionLogDerivative (2 * N) (2 * N) 0 τ +
      torsionLogDerivative (2 * N) N N τ +
      torsionLogDerivative (2 * N) (2 * N) N τ ≠
        (2 : ℂ) * torsionLogDerivative N N 0 τ := by
  have hN : (0 : ℤ) < N := by exact_mod_cast NeZero.pos N
  have hn : ¬ (2 * N : ℤ) ∣ (N : ℤ) := by
    intro h
    exact (Int.le_of_dvd hN h).not_gt (by omega)
  have h10 : ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.Good (2 * N) ((N : ℤ), 0) :=
    fun h => hn h.1
  have h11 : ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.Good (2 * N) ((N : ℤ), (N : ℤ)) :=
    fun h => hn h.1
  have h21 : ZInQ.Contrib.HeckePrimeRationality.AllLevelForms.Good (2 * N) ((2 * N : ℤ), (N : ℤ)) :=
    fun h => hn h.2
  have hraw := raw_lattice_row (2 * N) τ
  push_cast at hraw
  rw [half_order_zero N N 0 h10 (by exact ⟨1, by ring⟩) (dvd_zero _) τ,
    half_order_zero N N N h11 (by exact ⟨1, by ring⟩) (by exact ⟨1, by ring⟩) τ,
    half_order_zero N (2 * N) N h21 (by exact ⟨2, by ring⟩) (by exact ⟨1, by ring⟩) τ,
    hraw, raw_lattice_row N τ]
  norm_num

end ZInQ.Contrib.HeckePrimeRationality.AllLevelTraceTwoZeroConvention
