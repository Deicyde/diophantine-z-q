import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.FiniteLinearDescent
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Coefficient-field saturation under a nonzero formal denominator

A linear retraction of the ambient field to the coefficient field acts on
all coefficients and on each finite convolution row. Cancellation in the
actual power-series domain then proves field membership of the quotient.
The denominator need not have a nonzero constant coefficient.
-/

noncomputable section
set_option autoImplicit false

namespace DirectCoefficientSaturation

/-- A nonzero field-valued denominator and a field-valued product force every
coefficient of the other factor into the same actual intermediate field. -/
theorem coefficients_mem_of_nonzero_mul
    (K : IntermediateField ℚ ℂ) (A B : PowerSeries ℂ) (hA0 : A ≠ 0)
    (hA : ∀ n : ℕ, A.coeff n ∈ K)
    (hAB : ∀ n : ℕ, (A * B).coeff n ∈ K) :
    ∀ n : ℕ, B.coeff n ∈ K := by
  classical
  let φ : K →+* ℂ := algebraMap K ℂ
  let L : K →ₗ[K] ℂ := Algebra.linearMap K ℂ
  have hker : LinearMap.ker L = ⊥ := by
    exact LinearMap.ker_eq_bot.mpr (algebraMap K ℂ).injective
  obtain ⟨P, hP⟩ := L.exists_leftInverse_of_injective hker
  have hPφ (a : K) : P (a : ℂ) = a := by
    have h := DFunLike.congr_fun hP a
    change P ((algebraMap K ℂ) a) = a at h
    simpa only [IntermediateField.algebraMap_apply] using h
  have hmul (a : K) (z : ℂ) : P ((a : ℂ) * z) = a * P z := by
    change P (a • z) = a • P z
    exact P.map_smul a z
  let aK : PowerSeries K := PowerSeries.mk (fun n => ⟨A.coeff n, hA n⟩)
  let bK : PowerSeries K := PowerSeries.mk (fun n => P (B.coeff n))
  let cK : PowerSeries K := PowerSeries.mk (fun n => ⟨(A * B).coeff n, hAB n⟩)
  have haK : PowerSeries.map φ aK = A := by
    ext n
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk, aK, φ,
      IntermediateField.algebraMap_apply]
  have hcK : PowerSeries.map φ cK = A * B := by
    ext n
    simp only [PowerSeries.coeff_map, PowerSeries.coeff_mk, cK, φ,
      IntermediateField.algebraMap_apply]
  have hprod : aK * bK = cK := by
    apply PowerSeries.ext
    intro n
    have hcp : cK.coeff n = P ((A * B).coeff n) := by
      simpa only [cK, PowerSeries.coeff_mk] using (hPφ ⟨(A * B).coeff n, hAB n⟩).symm
    rw [PowerSeries.coeff_mul, hcp, PowerSeries.coeff_mul, map_sum]
    apply Finset.sum_congr rfl
    intro ij _
    simp only [aK, bK, PowerSeries.coeff_mk]
    exact (hmul ⟨A.coeff ij.1, hA ij.1⟩ (B.coeff ij.2)).symm
  have hprodC : A * PowerSeries.map φ bK = A * B := by
    calc
      A * PowerSeries.map φ bK = PowerSeries.map φ aK * PowerSeries.map φ bK := by rw [haK]
      _ = PowerSeries.map φ (aK * bK) := (map_mul _ _ _).symm
      _ = PowerSeries.map φ cK := congrArg (PowerSeries.map φ) hprod
      _ = A * B := hcK
  have hzero : A * (PowerSeries.map φ bK - B) = 0 := by
    rw [mul_sub, hprodC, sub_self]
  have hbK : PowerSeries.map φ bK = B :=
    sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left hA0)
  intro n
  have hn := congrArg (fun s : PowerSeries ℂ => s.coeff n) hbK
  rw [PowerSeries.coeff_map] at hn
  rw [← hn]
  exact (bK.coeff n).property

end DirectCoefficientSaturation
