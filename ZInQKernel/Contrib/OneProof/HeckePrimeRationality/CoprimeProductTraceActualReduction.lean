import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.CoprimeProductTraceSplitFourier

/-!
# Actual determinant-pair torsion products reduce to correlations

The original actual λ-values are used throughout. Their proved -1/(pN)
Fourier identity and the exact determinant-line cancellation reduce the
rank-two orbit sum to a finite complex combination of nonzero-T correlations.
No lower correlation or product-span membership is assumed.
-/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane
open scoped BigOperators

namespace ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace

open TorsionCorrelation

abbrev DeterminantPairs (p : ℕ) (d : ZMod p) :=
  Σ T : {T : Point p // T ≠ 0}, {U : Point p // det T.val U = d}

/-- The actual finite determinant-pair orbit sum of λ-products. -/
def determinantOrbitValue (p N : ℕ) [Fact p.Prime] (τ : ℍ) (d : ZMod p) (A B : Point N) : ℂ := by
  classical
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ∑ D : DeterminantPairs p d, splitLambda p N τ A D.1.val * splitLambda p N τ B D.2.val

/-- Actual nonzero-prime-point rank-one correlation. -/
def nonzeroCorrelationValue (p N : ℕ) [Fact p.Prime] (τ : ℍ) (s : ZMod p) (A B : Point N) : ℂ := by
  classical
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ∑ T : {T : Point p // T ≠ 0}, splitLambda p N τ A T.val * splitLambda p N τ B (scale s T.val)

/-- The rank-two reduction with the actual pairing and its exact -1/N factor. -/
theorem actual_determinant_orbit_reduction (p N : ℕ) [Fact p.Prime] [NeZero N]
    (hcop : Nat.Coprime p N) (τ : ℍ) (d : ZMod p) (A B : Point N) :
    determinantOrbitValue p N τ d A B = -(1 / (N : ℂ)) *
      ∑ C : Point N, pairing N (scale (p : ZMod N) C) B *
        ∑ s : ZMod p, phase p (-(N : ZMod p) * d * s) * nonzeroCorrelationValue p N τ s A C := by
  classical
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have he : (N : ZMod p) ≠ 0 := ((ZMod.isUnit_iff_coprime N p).mpr hcop.symm).ne_zero
  have hfirst : determinantOrbitValue p N τ d A B = -(1 / ((p * N : ℕ) : ℂ)) *
      ∑ C : Point N, pairing N (scale (p : ZMod N) C) B *
        ∑ D : DeterminantPairs p d, splitLambda p N τ A D.1.val *
          ∑ V : Point p, splitLambda p N τ C V * pairing p (scale (N : ZMod p) V) D.2.val := by
    unfold determinantOrbitValue
    simp_rw [split_lambda_fourier p N hcop τ B, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro C _
    apply Finset.sum_congr rfl
    intro D _
    apply Finset.sum_congr rfl
    intro V _
    ring
  have hpair (C : Point N) :
      (∑ D : DeterminantPairs p d, splitLambda p N τ A D.1.val *
        ∑ V : Point p, splitLambda p N τ C V * pairing p (scale (N : ZMod p) V) D.2.val) =
      ∑ s : ZMod p, (p : ℂ) * phase p (-(N : ZMod p) * d * s) *
        nonzeroCorrelationValue p N τ s A C := by
    rw [Fintype.sum_sigma]
    simp_rw [← Finset.mul_sum]
    exact determinant_pair_reduction p (N : ZMod p) he d
      (splitLambda p N τ A) (splitLambda p N τ C)
  rw [hfirst]
  simp_rw [hpair, mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro C _
  apply Finset.sum_congr rfl
  intro s _
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  push_cast
  field_simp

/-- The same actual reduction in the recomputed negative exponential phase. -/
theorem actual_determinant_orbit_reduction_exp (p N : ℕ) [Fact p.Prime] [NeZero N]
    (hcop : Nat.Coprime p N) (τ : ℍ) (d : ZMod p) (A B : Point N) :
    determinantOrbitValue p N τ d A B = -(1 / (N : ℂ)) *
      ∑ C : Point N, pairing N (scale (p : ZMod N) C) B *
        ∑ s : ZMod p, Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (N : ℂ) *
          (d.val : ℂ) * (s.val : ℂ) / (p : ℂ)) * nonzeroCorrelationValue p N τ s A C := by
  let : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [actual_determinant_orbit_reduction p N hcop τ d A B]
  simp_rw [determinant_phase_exp p N]

end ZInQ.Contrib.HeckePrimeRationality.CoprimeProductTrace
