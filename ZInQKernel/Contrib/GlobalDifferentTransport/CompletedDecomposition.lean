/-
# Actual decomposition group and completed-field Galois group

A completed field automorphism is continuous by proved finite-dimensionality.
Its global normal-field restriction preserves the selected prime because the
prime is exactly the set of global integers whose powers converge to zero.
Density then recovers the given completed automorphism. No local-degree count,
assumed valuation preservation, or Kronecker-Weber premise is used.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.CompletedGalois
public import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The genuine field decomposition equivalence and integer/fraction compatibility

The forward action is the original canonical `decompositionFieldHom`. The inverse
is named restriction to the normal global number field with proved stabilizer
membership. Integer automorphisms extend by the original actual fraction-field
map; completed field automorphisms restrict to the actual integer action. Every
commuting square is stated on the concrete rings and fields.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField Filter
open scoped NumberField Pointwise GlobalDifferentTransportCompletion Valued Topology

namespace GlobalDifferentTransport

variable (L : Type*) [Field L] [NumberField L]
  (v : HeightOneSpectrum ℤ) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- The actual global prime is detected by topological nilpotence of the actual completed
integer image. This uses the existing normalized valuation and the same completed topology. -/
theorem mem_prime_iff_tendsto_completedInteger_pow (a : 𝓞 L) :
    a ∈ w.asIdeal ↔ Tendsto (fun n : ℕ ↦ (algebraMap (𝓞 L) (w.adicCompletion L) a) ^ n)
      atTop (𝓝 0) := by
  rw [tendsto_pow_atTop_nhds_zero_iff_norm_lt_one, Valued.toNormedField.norm_lt_one_iff]
  change a ∈ w.asIdeal ↔
    Valued.v (algebraMap (𝓞 L) (w.adicCompletionIntegers L) a : w.adicCompletion L) < 1
  rw [valued_completed_globalInteger (L := L) (w := w), w.intValuation_lt_one_iff_mem]

variable [Normal ℚ L]

/-- Restriction of the actual completed field automorphism to the normal global field. -/
def completedFieldRestrictionHom :
    (w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) →* Gal(L/ℚ) :=
  (AlgEquiv.restrictNormalHom L).comp (AlgEquiv.restrictScalarsHom ℚ)

/-- The exact normal-field restriction, as an automorphism rather than a homomorphism value. -/
abbrev globalAutOfCompletedField
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) : Gal(L/ℚ) :=
  completedFieldRestrictionHom L v w τ

/-- The global restriction and the actual completed field map commute on every global element. -/
theorem globalAutOfCompletedField_algebraMap
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) (x : L) :
    algebraMap L (w.adicCompletion L) (globalAutOfCompletedField L v w τ x) =
      τ (algebraMap L (w.adicCompletion L) x) :=
  AlgEquiv.restrictNormal_commutes (τ.restrictScalars ℚ) L x

/-- The same actual square on the genuine global integer ring. -/
theorem globalAutOfCompletedField_integer_algebraMap
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) (a : 𝓞 L) :
    algebraMap (𝓞 L) (w.adicCompletion L) (globalAutOfCompletedField L v w τ • a) =
      τ (algebraMap (𝓞 L) (w.adicCompletion L) a) := by
  change algebraMap L (w.adicCompletion L)
      (globalAutOfCompletedField L v w τ (algebraMap (𝓞 L) L a)) = _
  exact globalAutOfCompletedField_algebraMap L v w τ _

/-- Continuity of the actual completed field automorphism forces its global restriction to
preserve the selected prime. No field-automorphism valuation theorem is assumed here. -/
theorem globalAutOfCompletedField_maps_prime
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L)
    (a : 𝓞 L) (ha : a ∈ w.asIdeal) : globalAutOfCompletedField L v w τ • a ∈ w.asIdeal := by
  apply (mem_prime_iff_tendsto_completedInteger_pow L w _).mpr
  have hpowers := (mem_prime_iff_tendsto_completedInteger_pow L w a).mp ha
  have h := ((continuous_completedFieldAut L v w τ).tendsto (0 : w.adicCompletion L)).comp hpowers
  simpa only [Function.comp_def, map_pow, map_zero,
    ← globalAutOfCompletedField_integer_algebraMap] using h

/-- The global normal restriction preserves and reflects membership in the actual prime. -/
theorem globalAutOfCompletedField_mem_prime_iff
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) (a : 𝓞 L) :
    globalAutOfCompletedField L v w τ • a ∈ w.asIdeal ↔ a ∈ w.asIdeal := by
  constructor
  · intro ha
    have hinv : globalAutOfCompletedField L v w τ.symm =
        (globalAutOfCompletedField L v w τ)⁻¹ := (completedFieldRestrictionHom L v w).map_inv τ
    have h := globalAutOfCompletedField_maps_prime L v w τ.symm
      (globalAutOfCompletedField L v w τ • a) ha
    simpa only [hinv, inv_smul_smul] using h
  · exact globalAutOfCompletedField_maps_prime L v w τ a

/-- The actual global normal restriction belongs to the genuine decomposition subgroup. -/
theorem globalAutOfCompletedField_mem_stabilizer
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) :
    globalAutOfCompletedField L v w τ ∈ decompositionGroup L w := by
  rw [MulAction.mem_stabilizer_iff, Ideal.pointwise_smul_def]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (globalAutOfCompletedField_mem_prime_iff L v w τ a).mpr ha
  · intro a ha
    have h : (globalAutOfCompletedField L v w τ)⁻¹ • a ∈ w.asIdeal :=
      (globalAutOfCompletedField_mem_prime_iff L v w τ _).mp (by simpa using ha)
    simpa using Ideal.mem_map_of_mem
      (MulSemiringAction.toRingHom Gal(L/ℚ) (𝓞 L) (globalAutOfCompletedField L v w τ)) h

/-- The named actual inverse of the completion action: normal restriction with its proved
membership in the selected decomposition group. -/
def decompositionOfCompletedFieldAut
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) : decompositionGroup L w :=
  ⟨globalAutOfCompletedField L v w τ, globalAutOfCompletedField_mem_stabilizer L v w τ⟩

/-- Restricting the old canonical field action recovers the original global automorphism. -/
theorem completedFieldRestrictionHom_decompositionFieldHom (σ : decompositionGroup L w) :
    completedFieldRestrictionHom L v w (decompositionFieldHom L v w σ) = (σ : Gal(L/ℚ)) := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap L (w.adicCompletion L)).injective
  rw [globalAutOfCompletedField_algebraMap, decompositionFieldHom_algebraMap]

/-- Completing the named actual inverse recovers every actual completed field automorphism.
The proof is continuous equality on the dense global field, not a cardinality assumption. -/
theorem decompositionFieldHom_decompositionOfCompletedFieldAut
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) :
    decompositionFieldHom L v w (decompositionOfCompletedFieldAut L v w τ) = τ := by
  apply DFunLike.coe_injective
  apply (w.denseRange_algebraMap L).equalizer
    (continuous_completionDecompositionRingEquiv L w (decompositionOfCompletedFieldAut L v w τ))
    (continuous_completedFieldAut L v w τ)
  funext x
  change decompositionFieldHom L v w (decompositionOfCompletedFieldAut L v w τ)
    (algebraMap L (w.adicCompletion L) x) = τ (algebraMap L (w.adicCompletion L) x)
  rw [decompositionFieldHom_algebraMap]
  exact globalAutOfCompletedField_algebraMap L v w τ x

/-- Genuine surjectivity of the original canonical decomposition-field action. -/
theorem decompositionFieldHom_surjective : Function.Surjective (decompositionFieldHom L v w) :=
  fun τ ↦ ⟨decompositionOfCompletedFieldAut L v w τ,
    decompositionFieldHom_decompositionOfCompletedFieldAut L v w τ⟩

/-- The actual global decomposition group is the actual completed-field Galois group, with a
named forward action and named inverse restriction on the correct canonical base algebra. -/
def decompositionFieldMulEquiv : decompositionGroup L w ≃*
    (w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) where
  toFun := decompositionFieldHom L v w
  invFun := decompositionOfCompletedFieldAut L v w
  left_inv σ := Subtype.ext (completedFieldRestrictionHom_decompositionFieldHom L v w σ)
  right_inv := decompositionFieldHom_decompositionOfCompletedFieldAut L v w
  map_mul' := (decompositionFieldHom L v w).map_mul

/-- The field equivalence is exactly the original constructed completion action. -/
theorem decompositionFieldMulEquiv_apply (σ : decompositionGroup L w) :
    decompositionFieldMulEquiv L v w σ = decompositionFieldHom L v w σ := rfl

/-- Its inverse is exactly the named global normal restriction with proved stabilizer membership. -/
theorem decompositionFieldMulEquiv_symm_apply
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) :
    (decompositionFieldMulEquiv L v w).symm τ = decompositionOfCompletedFieldAut L v w τ := rfl

/-- Every actual completed field automorphism preserves the actual normalized valuation,
derived from the genuine decomposition equivalence rather than used as its premise. -/
theorem valued_completedFieldAut
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) (x : w.adicCompletion L) :
    Valued.v (τ x) = Valued.v x := by
  rw [← decompositionFieldHom_decompositionOfCompletedFieldAut L v w τ]
  exact valued_completionDecompositionRingEquiv L w (decompositionOfCompletedFieldAut L v w τ) x

/-- The actual restriction of a completed field automorphism to completed integers. -/
def integerAutOfCompletedFieldAut
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) :
    w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ] w.adicCompletionIntegers L :=
  decompositionIntegersHom L v w (decompositionOfCompletedFieldAut L v w τ)

/-- The integer restriction is literally the given field automorphism on every integer image. -/
theorem integerAutOfCompletedFieldAut_algebraMap
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L)
    (x : w.adicCompletionIntegers L) :
    algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) (integerAutOfCompletedFieldAut L v w τ x) =
      τ (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) x) := by
  change decompositionFieldHom L v w (decompositionOfCompletedFieldAut L v w τ)
    (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) x) = _
  rw [decompositionFieldHom_decompositionOfCompletedFieldAut L v w τ]

/-- The original fraction-field extension of integer automorphisms, as an actual group map. -/
def integerToCompletedFieldHom :
    (w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ] w.adicCompletionIntegers L) →*
      (w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) where
  toFun := fractionAutOfIntegerAut L v w
  map_one' := by
    apply AlgEquiv.toRingEquiv_injective
    apply RingEquiv.toRingHom_injective
    apply IsFractionRing.ringHom_ext (A := w.adicCompletionIntegers L)
    intro x
    change fractionAutOfIntegerAut L v w 1
      (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) x) = _
    rw [fractionAutOfIntegerAut_algebraMap]
    rfl
  map_mul' σ τ := by
    apply AlgEquiv.toRingEquiv_injective
    apply RingEquiv.toRingHom_injective
    apply IsFractionRing.ringHom_ext (A := w.adicCompletionIntegers L)
    intro x
    change fractionAutOfIntegerAut L v w (σ * τ)
      (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) x) =
        fractionAutOfIntegerAut L v w σ (fractionAutOfIntegerAut L v w τ
          (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) x))
    rw [fractionAutOfIntegerAut_algebraMap, fractionAutOfIntegerAut_algebraMap,
      fractionAutOfIntegerAut_algebraMap]
    rfl

/-- Integer restriction and the original fraction extension are inverse on the actual field. -/
theorem fractionAut_integerAutOfCompletedFieldAut
    (τ : w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) :
    fractionAutOfIntegerAut L v w (integerAutOfCompletedFieldAut L v w τ) = τ := by
  apply AlgEquiv.toRingEquiv_injective
  apply RingEquiv.toRingHom_injective
  apply IsFractionRing.ringHom_ext (A := w.adicCompletionIntegers L)
  intro x
  change fractionAutOfIntegerAut L v w (integerAutOfCompletedFieldAut L v w τ)
    (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) x) = _
  rw [fractionAutOfIntegerAut_algebraMap, integerAutOfCompletedFieldAut_algebraMap]
  rfl

/-- The same inverse identity on the actual completed integer ring. -/
theorem integerAutOfCompletedFieldAut_fractionAut
    (ρ : w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ] w.adicCompletionIntegers L) :
    integerAutOfCompletedFieldAut L v w (fractionAutOfIntegerAut L v w ρ) = ρ := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)
    (integerAutOfCompletedFieldAut L v w (fractionAutOfIntegerAut L v w ρ) x) = _
  rw [integerAutOfCompletedFieldAut_algebraMap, fractionAutOfIntegerAut_algebraMap]
  rfl

/-- The completed integer and completed field automorphism groups are genuinely equivalent
via their named actual fraction extension and actual integer restriction maps. -/
def completedIntegerFieldAutMulEquiv :
    (w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ] w.adicCompletionIntegers L) ≃*
      (w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L) where
  toFun := integerToCompletedFieldHom L v w
  invFun := integerAutOfCompletedFieldAut L v w
  left_inv := integerAutOfCompletedFieldAut_fractionAut L v w
  right_inv := fractionAut_integerAutOfCompletedFieldAut L v w
  map_mul' := (integerToCompletedFieldHom L v w).map_mul

end GlobalDifferentTransport
