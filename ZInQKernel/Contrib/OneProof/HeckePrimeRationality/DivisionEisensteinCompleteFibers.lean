import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinLowerClosureOne
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelWeierstrassDistributionNat

/-!
# Complete torsion fibres as genuine lower-level series combinations

The actual Weierstrass distribution theorem reduces complete upper torsion
fibres to lower series generators. The identities below concern entire fibres,
not a claim that every principal-congruence orbit is such a fibre.
-/

noncomputable section
set_option autoImplicit false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure

open EisensteinWeightTwo DivisionEisensteinLevelMaps

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- The complete actual upper torsion fibre over an arbitrary lower label. -/
def completeFiber (t N : ℕ) (ht : 0 < t) (hN : 0 < N) (a b : ℤ) :
    _root_.ModularForm (ΓP (t * N)) 2 :=
  ∑ r : Fin t, ∑ s : Fin t, divisionEisensteinMF (t * N) (Nat.mul_pos ht hN)
    ![a + (N : ℤ) * (r : ℕ), b + (N : ℤ) * (s : ℕ)]

/-- Genuine all-label complete-fibre reduction, with its exact weight-two factor t². -/
theorem completeFiber_eq_restriction (t N : ℕ) (ht : 0 < t) (hN : 0 < N) (a b : ℤ) :
    completeFiber t N ht hN a b = restriction N (t * N) (dvd_mul_left N t)
      ((t : ℂ) ^ 2 • divisionEisensteinMF N hN ![a,b]) := by
  apply _root_.ModularForm.ext
  intro τ
  rw [restriction_apply]
  simp only [completeFiber, sum_apply, smul_apply, smul_eq_mul, divisionEisensteinMF_eq_xValue_all]
  exact WeierstrassDistributionNat.x_distribution_nat t N ht hN τ a b

/-- A complete actual fibre traces to a lower series generator, with no orbit premise. -/
theorem normalizedTrace_completeFiber (t N : ℕ) (ht : 0 < t) (hN : 0 < N) (a b : ℤ) :
    normalizedTrace N (t * N) (Nat.mul_pos ht hN) (completeFiber t N ht hN a b) =
      (t : ℂ) ^ 2 • divisionEisensteinMF N hN ![a,b] := by
  rw [completeFiber_eq_restriction,
    normalizedTrace_restriction (Nat.mul_pos ht hN) (dvd_mul_left N t)]

theorem normalizedTrace_completeFiber_mem (t N : ℕ) (ht : 0 < t) (hN : 0 < N) (a b : ℤ) :
    normalizedTrace N (t * N) (Nat.mul_pos ht hN) (completeFiber t N ht hN a b) ∈ seriesSpan N hN := by
  rw [normalizedTrace_completeFiber]
  exact Submodule.smul_mem _ _ (generator_mem_seriesSpan N hN ![a,b])

/-- Complete-fibre combinations are a nontrivial explicit upper subspace
whose actual trace belongs to the lower series span. -/
theorem normalizedTrace_mem_of_completeFiber_span (t N : ℕ) (ht : 0 < t) (hN : 0 < N)
    {f : _root_.ModularForm (ΓP (t * N)) 2}
    (hf : f ∈ Submodule.span ℂ (Set.range (fun a : ℤ × ℤ => completeFiber t N ht hN a.1 a.2))) :
    normalizedTrace N (t * N) (Nat.mul_pos ht hN) f ∈ seriesSpan N hN := by
  have hle : Submodule.span ℂ (Set.range (fun a : ℤ × ℤ => completeFiber t N ht hN a.1 a.2)) ≤
      (seriesSpan N hN).comap (normalizedTrace N (t * N) (Nat.mul_pos ht hN)) := by
    apply Submodule.span_le.mpr
    rintro f ⟨a, rfl⟩
    exact normalizedTrace_completeFiber_mem t N ht hN a.1 a.2
  exact hle hf

/-- The all-label generator evaluation is compatible with known multiplicative
labels; both sides retain the actual series constructors. -/
theorem series_scaled_label (t N : ℕ) (ht : 0 < t) (hN : 0 < N) (a b : ℤ) :
    divisionEisensteinMF (t * N) (Nat.mul_pos ht hN) ![(t : ℤ) * a, (t : ℤ) * b] =
      restriction N (t * N) (dvd_mul_left N t) (divisionEisensteinMF N hN ![a,b]) := by
  have h := restriction_generator_mul N t hN ht ![a,b]
  have he : (fun i : Fin 2 => (t : ℤ) * (![a,b] i)) = (![(t : ℤ) * a, (t : ℤ) * b] : Fin 2 → ℤ) := by
    ext i; fin_cases i <;> rfl
  rw [he] at h
  exact h.symm

/-- Removing a scaled point from a complete fibre has an exact lower-level
reduction. Its geometric relation to a group orbit is not assumed. -/
theorem completeFiber_sub_scaled_generator (t N : ℕ) (ht : 0 < t) (hN : 0 < N)
    (a b c d : ℤ) :
    completeFiber t N ht hN a b -
      divisionEisensteinMF (t * N) (Nat.mul_pos ht hN) ![(t : ℤ) * c,(t : ℤ) * d] =
      restriction N (t * N) (dvd_mul_left N t)
        ((t : ℂ) ^ 2 • divisionEisensteinMF N hN ![a,b] - divisionEisensteinMF N hN ![c,d]) := by
  rw [completeFiber_eq_restriction t N ht hN a b, series_scaled_label t N ht hN c d, map_sub]

theorem normalizedTrace_completeFiber_sub_scaled_mem (t N : ℕ) (ht : 0 < t) (hN : 0 < N)
    (a b c d : ℤ) :
    normalizedTrace N (t * N) (Nat.mul_pos ht hN)
      (completeFiber t N ht hN a b - divisionEisensteinMF (t * N) (Nat.mul_pos ht hN)
        ![(t : ℤ) * c,(t : ℤ) * d]) ∈ seriesSpan N hN := by
  rw [completeFiber_sub_scaled_generator,
    normalizedTrace_restriction (Nat.mul_pos ht hN) (dvd_mul_left N t)]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (generator_mem_seriesSpan N hN ![a,b]))
    (generator_mem_seriesSpan N hN ![c,d])

end ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure
