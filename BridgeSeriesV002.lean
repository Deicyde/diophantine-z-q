import BridgeLambdaV002

/-!
# Coefficientwise field conjugation for genuine Fourier series

These operations act on proved field-valued coefficients, not on values of
holomorphic functions. Ring compatibility is derived from the actual field
lifts and their injective maps into complex power series.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace BridgeSeries

open BridgeDenominator

/-- Injectivity of the actual coefficient-field inclusion on all formal rows. -/
theorem fieldMap_injective (K : IntermediateField ℚ ℂ) :
    Function.Injective (PowerSeries.map (algebraMap K ℂ)) := by
  intro A B h
  apply PowerSeries.ext
  intro n
  apply Subtype.ext
  have hn := congrArg (fun s : PowerSeries ℂ => s.coeff n) h
  simpa only [PowerSeries.coeff_map, IntermediateField.algebraMap_apply] using hn

/-- Powers have coefficients in the same actual field. -/
theorem coefficients_mem_pow (K : IntermediateField ℚ ℂ) (A : PowerSeries ℂ)
    (hA : ∀ n : ℕ, A.coeff n ∈ K) (j : ℕ) : ∀ n : ℕ, (A ^ j).coeff n ∈ K := by
  induction j with
  | zero =>
      intro n
      rw [pow_zero, PowerSeries.coeff_one]
      split_ifs
      · exact K.one_mem
      · exact K.zero_mem
  | succ j hj =>
      rw [pow_succ]
      exact coefficients_mem_mul K _ _ hj hA

/-- The canonical membership lift preserves the actual product, including nonunits. -/
theorem coefficientLift_mul (K : IntermediateField ℚ ℂ) (A B : PowerSeries ℂ)
    (hA : ∀ n : ℕ, A.coeff n ∈ K) (hB : ∀ n : ℕ, B.coeff n ∈ K) :
    coefficientLift K (A * B) (coefficients_mem_mul K A B hA hB) =
      coefficientLift K A hA * coefficientLift K B hB := by
  apply fieldMap_injective K
  rw [map_mul, coefficientLift_map, coefficientLift_map, coefficientLift_map]

/-- The canonical lift also preserves every nonnegative power. -/
theorem coefficientLift_pow (K : IntermediateField ℚ ℂ) (A : PowerSeries ℂ)
    (hA : ∀ n : ℕ, A.coeff n ∈ K) (j : ℕ) :
    coefficientLift K (A ^ j) (coefficients_mem_pow K A hA j) =
      (coefficientLift K A hA) ^ j := by
  apply fieldMap_injective K
  rw [map_pow, coefficientLift_map, coefficientLift_map]

/-- Coefficient conjugation is a map of a proved field lift, not a pointwise analytic operation. -/
def conjugateSeries (K : IntermediateField ℚ ℂ) (σ : K ≃ₐ[ℚ] K)
    (A : PowerSeries ℂ) (hA : ∀ n : ℕ, A.coeff n ∈ K) : PowerSeries ℂ :=
  PowerSeries.map ((algebraMap K ℂ).comp σ.toRingHom) (coefficientLift K A hA)

/-- Its literal coefficient identity. -/
theorem conjugateSeries_coeff (K : IntermediateField ℚ ℂ) (σ : K ≃ₐ[ℚ] K)
    (A : PowerSeries ℂ) (hA : ∀ n : ℕ, A.coeff n ∈ K) (n : ℕ) :
    (conjugateSeries K σ A hA).coeff n = (σ (⟨A.coeff n, hA n⟩ : K) : ℂ) := by
  simp only [conjugateSeries, coefficientLift, PowerSeries.coeff_map,
    PowerSeries.coeff_mk, RingHom.comp_apply, IntermediateField.algebraMap_apply]
  rfl

/-- Multiplication compatibility is proved on all coefficient equations at once. -/
theorem conjugateSeries_mul (K : IntermediateField ℚ ℂ) (σ : K ≃ₐ[ℚ] K)
    (A B : PowerSeries ℂ) (hA : ∀ n : ℕ, A.coeff n ∈ K)
    (hB : ∀ n : ℕ, B.coeff n ∈ K) :
    conjugateSeries K σ (A * B) (coefficients_mem_mul K A B hA hB) =
      conjugateSeries K σ A hA * conjugateSeries K σ B hB := by
  rw [conjugateSeries, coefficientLift_mul, map_mul]
  rfl

/-- Power compatibility for the actual coefficient operation. -/
theorem conjugateSeries_pow (K : IntermediateField ℚ ℂ) (σ : K ≃ₐ[ℚ] K)
    (A : PowerSeries ℂ) (hA : ∀ n : ℕ, A.coeff n ∈ K) (j : ℕ) :
    conjugateSeries K σ (A ^ j) (coefficients_mem_pow K A hA j) =
      (conjugateSeries K σ A hA) ^ j := by
  rw [conjugateSeries, coefficientLift_pow, map_pow]
  rfl

/-- Rational coefficients are fixed, through the actual rational algebra maps. -/
theorem conjugateSeries_eq_of_rational (K : IntermediateField ℚ ℂ) (σ : K ≃ₐ[ℚ] K)
    (A : PowerSeries ℂ) (hA : ∀ n : ℕ, A.coeff n ∈ K)
    (hQ : ∀ n : ℕ, ∃ q : ℚ, A.coeff n = (q : ℂ)) :
    conjugateSeries K σ A hA = A := by
  ext n
  rw [conjugateSeries_coeff]
  obtain ⟨q, hq⟩ := hQ n
  have hqmap := (Rat.castHom ℂ).map_rat_algebraMap q
  change (q : ℂ) = algebraMap ℚ ℂ q at hqmap
  have hqA := hq.trans hqmap
  have hs : (⟨A.coeff n, hA n⟩ : K) = algebraMap ℚ K q := by
    apply Subtype.ext
    simpa only [IntermediateField.coe_algebraMap_apply] using hqA
  rw [hs, σ.commutes]
  simpa only [IntermediateField.coe_algebraMap_apply] using hqA.symm

/-- Conjugation produces coefficients in the same field. -/
theorem conjugateSeries_coefficients_mem (K : IntermediateField ℚ ℂ) (σ : K ≃ₐ[ℚ] K)
    (A : PowerSeries ℂ) (hA : ∀ n : ℕ, A.coeff n ∈ K) (n : ℕ) :
    (conjugateSeries K σ A hA).coeff n ∈ K := by
  rw [conjugateSeries_coeff]
  exact (σ _).property

end BridgeSeries
