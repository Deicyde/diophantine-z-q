import FrobLift.ResidueFiniteV002

/-!
# The finite place of a discrete valuation subring of a number field

For `K` a number field and `O ⊆ K` a discrete valuation subring, `𝔭 = 𝓞 K ∩ 𝔪_O` is a nonzero
maximal ideal of `𝓞 K`, `O` is the localization of `𝓞 K` at `𝔭` (as subsets of `K`:
`y ∈ O ↔ s y = a` for some `a, s ∈ 𝓞 K` with `s ∉ 𝔭`), the residue field of `O` is `𝓞 K / 𝔭`, and
its cardinality is the absolute norm of `𝔭`.
-/

noncomputable section

namespace FrobLift

open NumberField

variable {K : Type*} [Field K] [NumberField K] (O : ValuationSubring K) [IsDiscreteValuationRing O]

/-- The prime `𝔭 = 𝓞 K ∩ 𝔪_O`. -/
abbrev placePrime : Ideal (𝓞 K) := RingHom.ker (resHom O)

theorem mem_placePrime_iff (a : 𝓞 K) :
    a ∈ placePrime O ↔ O.valuation (algebraMap (𝓞 K) K a) < 1 := by
  rw [placePrime, RingHom.mem_ker, resHom_eq_zero_iff]

theorem placePrime_ne_bot : placePrime O ≠ ⊥ := by
  obtain ⟨y, hyM, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (IsDiscreteValuationRing.not_a_field' (R := O))
  obtain ⟨s, a, hs, ha⟩ := exists_unit_denom_ringOfIntegers O y.1 y.2
  intro hbot
  have haker : a ∈ placePrime O := by
    rw [mem_placePrime_iff, ← ha, Valuation.map_mul, hs, one_mul]
    exact (ValuationSubring.valuation_lt_one_iff O y).mp hyM
  rw [hbot, Ideal.mem_bot] at haker
  have h0 : algebraMap (𝓞 K) K s * (y : K) = 0 := by rw [ha, haker, map_zero]
  rcases mul_eq_zero.mp h0 with h | h
  · rw [h, map_zero] at hs
    exact zero_ne_one hs
  · exact hy0 (Subtype.ext h)

instance placePrime_isPrime : (placePrime O).IsPrime := RingHom.ker_isPrime _

instance placePrime_isMaximal : (placePrime O).IsMaximal :=
  (placePrime_isPrime O).isMaximal (placePrime_ne_bot O)

/-- **`O` is the localization of `𝓞 K` at `𝔭`.** -/
theorem mem_iff_exists_den (y : K) :
    y ∈ O ↔ ∃ s a : 𝓞 K, s ∉ placePrime O ∧ algebraMap (𝓞 K) K s * y = algebraMap (𝓞 K) K a := by
  constructor
  · intro hy
    obtain ⟨s, a, hs, ha⟩ := exists_unit_denom_ringOfIntegers O y hy
    refine ⟨s, a, ?_, ha⟩
    rw [mem_placePrime_iff, hs]
    exact lt_irrefl 1
  · rintro ⟨s, a, hs, ha⟩
    rw [mem_placePrime_iff, not_lt] at hs
    have hs1 : O.valuation (algebraMap (𝓞 K) K s) = 1 :=
      le_antisymm ((ValuationSubring.valuation_le_one_iff O _).2 (ringOfIntegers_mem O s)) hs
    rw [← ValuationSubring.valuation_le_one_iff]
    have hv := congrArg O.valuation ha
    rw [Valuation.map_mul, hs1, one_mul] at hv
    rw [hv]
    exact (ValuationSubring.valuation_le_one_iff O _).2 (ringOfIntegers_mem O a)

/-- The residue field of `O` is `𝓞 K / 𝔭`. -/
def residueEquiv : 𝓞 K ⧸ placePrime O ≃+* IsLocalRing.ResidueField O := by
  refine RingEquiv.ofBijective (RingHom.kerLift (resHom O)) ⟨RingHom.kerLift_injective _, ?_⟩
  intro r
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective r
  obtain ⟨s, a, hs, ha⟩ := exists_unit_denom_ringOfIntegers O y.1 y.2
  have hsP : Ideal.Quotient.mk (placePrime O) s ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, mem_placePrime_iff, hs]
    exact lt_irrefl 1
  obtain ⟨t, ht⟩ := Ideal.Quotient.exists_inv hsP
  refine ⟨Ideal.Quotient.mk _ a * t, ?_⟩
  have h1 : resHom O s * RingHom.kerLift (resHom O) t = 1 := by
    rw [← RingHom.kerLift_mk, ← map_mul]
    exact (congrArg (RingHom.kerLift (resHom O)) ht).trans (map_one _)
  have h2 : resHom O s * IsLocalRing.residue O y = resHom O a := by
    rw [resHom_apply, resHom_apply, ← map_mul]
    congr 1
    exact Subtype.ext ha
  rw [map_mul, RingHom.kerLift_mk]
  linear_combination (-(RingHom.kerLift (resHom O) t)) * h2 + IsLocalRing.residue O y * h1

/-- **`q` is the absolute norm of `𝔭`.** -/
theorem card_residueField_eq_absNorm :
    Nat.card (IsLocalRing.ResidueField O) = Ideal.absNorm (placePrime O) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (residueEquiv O).toEquiv).symm

end FrobLift
