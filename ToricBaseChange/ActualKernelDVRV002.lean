import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# The generic point of a discrete valuation ring is open

For a discrete valuation ring `R` with fraction field `K` and a uniformizer `ϖ`, `K = R[1/ϖ]`
(`isLocalization_away_uniformizer`), so `Spec K → Spec R` is an open immersion
(`isOpenImmersion_generic`) whose image is the generic point (`generic_apply`). Also: a local ring has
`2` or `3` invertible (`exists_two_le_isUnit`).
-/

set_option linter.style.longLine false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace ToricBaseChange.ActualKernel

theorem isLocalization_away_uniformizer (R K : Type) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {ϖ : R}
    (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ K := by
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp hy
    apply isUnit_iff_ne_zero.mpr
    exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (pow_ne_zero n hϖ.ne_zero)
  · intro z
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) z
    have hb0' : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0' hϖ
    refine ⟨⟨a * ↑u⁻¹, ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
    have hb0 : algebraMap R K b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0'
    have huinv : algebraMap R K (↑u⁻¹ : R) * algebraMap R K (↑u : R) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    simp only
    rw [div_mul_eq_mul_div, div_eq_iff hb0, hu]
    simp only [map_mul]
    linear_combination (-(algebraMap R K a * algebraMap R K (ϖ ^ n))) * huinv
  · intro x y h
    exact ⟨1, by rw [IsFractionRing.injective R K h]⟩

variable {L : Type} [Field L]

/-- **`Spec L → Spec O'` is an open immersion** for a discrete valuation ring `O' ⊆ L`. -/
theorem isOpenImmersion_generic (O' : ValuationSubring L) [IsDiscreteValuationRing O'] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap O' L))) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O'
  haveI := isLocalization_away_uniformizer O' L hϖ
  exact IsOpenImmersion.of_isLocalization ϖ

/-- The point of `Spec L` maps to the generic point of `Spec O'`. -/
theorem generic_apply (O' : ValuationSubring L) (a : Spec (CommRingCat.of L)) :
    Spec.map (CommRingCat.ofHom (algebraMap O' L)) a = genericPoint (Spec (CommRingCat.of O')) := by
  rw [genericPoint_eq_bot_of_affine]
  let a' : PrimeSpectrum L := a
  change PrimeSpectrum.comap (algebraMap O' L) a' = ⊥
  apply PrimeSpectrum.ext
  rw [PrimeSpectrum.comap_asIdeal, Ideal.eq_bot_of_prime a'.asIdeal]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective O' L)

/-- In a local ring, `2` or `3` is invertible. -/
theorem exists_two_le_isUnit (R : Type) [CommRing R] [IsLocalRing R] :
    ∃ m : ℕ, 2 ≤ m ∧ IsUnit (m : R) := by
  by_cases h2 : IsUnit ((2 : ℕ) : R)
  · exact ⟨2, le_refl _, h2⟩
  · refine ⟨3, by norm_num, ?_⟩
    by_contra h3
    have hm2 : ((2 : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h2
    have hm3 : ((3 : ℕ) : R) ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h3
    have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      have := (IsLocalRing.maximalIdeal R).sub_mem hm3 hm2
      norm_num at this
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)

end ToricBaseChange.ActualKernel
