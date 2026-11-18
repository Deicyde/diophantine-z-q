import FrobLift.UnitDenominatorV001
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Polynomial.Content
import Mathlib.RingTheory.Localization.Integral

/-!
# The residue field of a discrete valuation subring of a number field is finite

`K` a number field, `O ⊆ K` a valuation subring which is a discrete valuation ring. Then
`𝓞 K ⊆ O`, every element of `O` is `a / s` with `a, s ∈ 𝓞 K` and `s` an `O`-unit (unit denominators
for a primitive integer polynomial), so the residue field of `O` is the image of `𝓞 K / 𝔭` for the
nonzero (hence maximal) prime `𝔭 = 𝓞 K ∩ 𝔪_O`, which is finite.
-/

noncomputable section

namespace FrobLift

open Polynomial NumberField

variable {K : Type*} [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]

theorem ringOfIntegers_mem (a : 𝓞 K) : algebraMap (𝓞 K) K a ∈ O := by
  have h : IsIntegral ℤ (algebraMap (𝓞 K) K a) := a.isIntegral_coe
  have h' : IsIntegral O (algebraMap (𝓞 K) K a) := h.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  rw [← hy]
  exact y.2

/-- **Unit denominators from the ring of integers.** -/
theorem exists_unit_denom_ringOfIntegers (y : K) (hy : y ∈ O) :
    ∃ s a : 𝓞 K, O.valuation (algebraMap (𝓞 K) K s) = 1 ∧
      algebraMap (𝓞 K) K s * y = algebraMap (𝓞 K) K a := by
  have halg : IsAlgebraic ℤ y :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨p, hp0, hpy⟩ := halg
  have hp'y : aeval y p.primPart = 0 := aeval_primPart_eq_zero hp0 hpy
  have hprim : p.primPart.IsPrimitive := isPrimitive_primPart p
  have hunit : ∃ i, O.valuation ((p.primPart.coeff i : ℤ) : K) = 1 := by
    by_contra hcon
    push_neg at hcon
    set I : Ideal ℤ := (IsLocalRing.maximalIdeal O).comap (algebraMap ℤ O) with hI
    have hmem : ∀ i, p.primPart.coeff i ∈ I := by
      intro i
      rw [hI, Ideal.mem_comap, ValuationSubring.valuation_lt_one_iff]
      have hle : O.valuation ((p.primPart.coeff i : ℤ) : K) ≤ 1 :=
        (ValuationSubring.valuation_le_one_iff O _).2 (intCast_mem O _)
      have hlt := lt_of_le_of_ne hle (hcon i)
      simpa using hlt
    have hdvd : C (Submodule.IsPrincipal.generator I) ∣ p.primPart := by
      rw [C_dvd_iff_dvd_coeff]
      intro i
      have h := hmem i
      rw [← Ideal.span_singleton_generator I, Ideal.mem_span_singleton] at h
      exact h
    have hu := hprim _ hdvd
    have htop : I = ⊤ := Ideal.eq_top_of_isUnit_mem I (Submodule.IsPrincipal.generator_mem I) hu
    exact Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal O).ne_top htop
  refine exists_unit_denominator O ?_ (ringOfIntegers_mem O) (p.primPart.map (algebraMap ℤ (𝓞 K)))
    hy (by rwa [aeval_map_algebraMap]) ?_
  · intro z hz
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hz
    exact ⟨y, hy⟩
  · obtain ⟨i, hi⟩ := hunit
    exact ⟨i, by simpa [coeff_map] using hi⟩

/-- The reduction map `𝓞 K → O / 𝔪_O`. -/
def resHom : 𝓞 K →+* IsLocalRing.ResidueField O :=
  (IsLocalRing.residue O).comp ((algebraMap (𝓞 K) K).codRestrict O (ringOfIntegers_mem O))

theorem resHom_apply (a : 𝓞 K) :
    resHom O a = IsLocalRing.residue O ⟨algebraMap (𝓞 K) K a, ringOfIntegers_mem O a⟩ := rfl

theorem resHom_eq_zero_iff (a : 𝓞 K) :
    resHom O a = 0 ↔ O.valuation (algebraMap (𝓞 K) K a) < 1 := by
  rw [resHom_apply, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]

/-- **The residue field of `O` is finite.** -/
theorem finite_residueField : Finite (IsLocalRing.ResidueField O) := by
  have hne : RingHom.ker (resHom O) ≠ ⊥ := by
    obtain ⟨y, hyM, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (IsDiscreteValuationRing.not_a_field' (R := O))
    obtain ⟨s, a, hs, ha⟩ := exists_unit_denom_ringOfIntegers O y.1 y.2
    intro hbot
    have haker : a ∈ RingHom.ker (resHom O) := by
      rw [RingHom.mem_ker, resHom_eq_zero_iff, ← ha, Valuation.map_mul, hs, one_mul]
      exact (ValuationSubring.valuation_lt_one_iff O y).mp hyM
    rw [hbot, Ideal.mem_bot] at haker
    have h0 : algebraMap (𝓞 K) K s * (y : K) = 0 := by rw [ha, haker, map_zero]
    rcases mul_eq_zero.mp h0 with h | h
    · rw [h, map_zero] at hs
      exact zero_ne_one hs
    · exact hy0 (Subtype.ext h)
  have hprime : (RingHom.ker (resHom O)).IsPrime := RingHom.ker_isPrime _
  haveI : (RingHom.ker (resHom O)).IsMaximal := hprime.isMaximal hne
  letI := Ideal.Quotient.field (RingHom.ker (resHom O))
  have hsurj : Function.Surjective (RingHom.kerLift (resHom O)) := by
    intro r
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
    obtain ⟨s, a, hs, ha⟩ := exists_unit_denom_ringOfIntegers O y.1 y.2
    have hs' : resHom O s ≠ 0 := by
      intro h
      rw [resHom_eq_zero_iff, hs] at h
      exact lt_irrefl _ h
    refine ⟨Ideal.Quotient.mk _ a * (Ideal.Quotient.mk _ s)⁻¹, ?_⟩
    rw [map_mul, map_inv₀, RingHom.kerLift_mk, RingHom.kerLift_mk, eq_comm,
      eq_mul_inv_iff_mul_eq₀ hs', resHom_apply, resHom_apply, ← map_mul]
    congr 1
    apply Subtype.ext
    show (y : K) * algebraMap (𝓞 K) K s = algebraMap (𝓞 K) K a
    rw [mul_comm]
    exact ha
  exact Finite.of_surjective _ hsurj

/-- The residue cardinality `q = #(O / 𝔪_O)` is at least `2`. -/
theorem two_le_card_residueField : 2 ≤ Nat.card (IsLocalRing.ResidueField O) := by
  haveI := finite_residueField O
  exact Finite.one_lt_card

end FrobLift
