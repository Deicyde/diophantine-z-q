/-
This contribution supplies the reverse restriction argument for the actual
completed-integer automorphism map. It uses Mathlib's normal-field restriction
and fraction-field extension, rather than assuming a local-degree count.
The forward map and selected completion proofs are attributed in Decomposition.lean.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.Decomposition

/-!
# Restriction from actual completed-integer automorphisms

An automorphism of the completed integer extension extends to its fraction
field, fixes the completed base fraction field, and restricts to the normal
global field. Exact contraction of the maximal ideal then places this global
automorphism in the actual decomposition subgroup. Density identifies its
continuous extension with the original local automorphism.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped NumberField Pointwise GlobalDifferentTransportCompletion Valued

namespace GlobalDifferentTransport

variable (L : Type*) [Field L] [NumberField L]
  (v : HeightOneSpectrum ℤ) (w : HeightOneSpectrum (𝓞 L)) [w.asIdeal.LiesOver v.asIdeal]

/-- A completed-integer automorphism extends to the actual fraction fields and fixes the
completed base field, because it fixes all completed base integers. -/
def fractionAutOfIntegerAut
    (τ : w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ]
      w.adicCompletionIntegers L) :
    w.adicCompletion L ≃ₐ[v.adicCompletion ℚ] w.adicCompletion L := by
  let E : w.adicCompletion L ≃+* w.adicCompletion L :=
    IsFractionRing.ringEquivOfRingEquiv τ.toRingEquiv
  have h : E.toRingHom.comp (algebraMap (v.adicCompletion ℚ) (w.adicCompletion L)) =
      algebraMap (v.adicCompletion ℚ) (w.adicCompletion L) := by
    apply IsFractionRing.ringHom_ext (A := v.adicCompletionIntegers ℚ)
    intro a
    change E (algebraMap (v.adicCompletion ℚ) (w.adicCompletion L)
      (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ) a)) = _
    rw [← IsScalarTower.algebraMap_apply (v.adicCompletionIntegers ℚ)
        (v.adicCompletion ℚ) (w.adicCompletion L),
      IsScalarTower.algebraMap_apply (v.adicCompletionIntegers ℚ)
        (w.adicCompletionIntegers L) (w.adicCompletion L)]
    rw [IsFractionRing.ringEquivOfRingEquiv_algebraMap]
    exact congrArg (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L))
      (τ.commutes a)
  exact AlgEquiv.ofRingEquiv (f := E) fun a ↦
    congrArg (fun f : v.adicCompletion ℚ →+* w.adicCompletion L ↦ f a) h

/-- The fraction-field extension agrees with the given automorphism on all local integers. -/
theorem fractionAutOfIntegerAut_algebraMap
    (τ : w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ]
      w.adicCompletionIntegers L) (x : w.adicCompletionIntegers L) :
    fractionAutOfIntegerAut L v w τ
        (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) x) =
      algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) (τ x) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap τ.toRingEquiv x

/-- The fraction-field automorphism is continuous by finite-dimensional topological linearity.
This uses the proved finite-dimensionality of the actual `ℤ`-based completed extension. -/
theorem continuous_fractionAutOfIntegerAut
    (τ : w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ]
      w.adicCompletionIntegers L) : Continuous (fractionAutOfIntegerAut L v w τ) := by
  let := moduleFinite_numberFieldCompletion L v w
  exact (fractionAutOfIntegerAut L v w τ).toLinearEquiv.toLinearMap.continuous_of_finiteDimensional

variable [Normal ℚ L]

/-- Normality of the global field permits restriction of the actual local fraction-field action. -/
def globalAutOfIntegerAut
    (τ : w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ]
      w.adicCompletionIntegers L) : Gal(L/ℚ) :=
  ((fractionAutOfIntegerAut L v w τ).restrictScalars ℚ).restrictNormal L

/-- This global restriction agrees with the original local automorphism on global integers. -/
theorem globalAutOfIntegerAut_commutes
    (τ : w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ]
      w.adicCompletionIntegers L) (a : 𝓞 L) :
    algebraMap (𝓞 L) (w.adicCompletionIntegers L)
        (globalAutOfIntegerAut L v w τ • a) =
      τ (algebraMap (𝓞 L) (w.adicCompletionIntegers L) a) := by
  apply Subtype.ext
  change algebraMap L (w.adicCompletion L)
      (globalAutOfIntegerAut L v w τ (algebraMap (𝓞 L) L a)) = _
  rw [globalAutOfIntegerAut, AlgEquiv.restrictNormal_commutes]
  change fractionAutOfIntegerAut L v w τ
      (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L a)) = _
  rw [← IsScalarTower.algebraMap_apply (𝓞 L) L (w.adicCompletion L)]
  change fractionAutOfIntegerAut L v w τ
    (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)
      (algebraMap (𝓞 L) (w.adicCompletionIntegers L) a)) =
      algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L)
        (τ (algebraMap (𝓞 L) (w.adicCompletionIntegers L) a))
  exact fractionAutOfIntegerAut_algebraMap L v w τ _

/-- The global restriction preserves membership in the chosen prime in both directions. -/
theorem globalAutOfIntegerAut_mem_prime_iff
    (τ : w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ]
      w.adicCompletionIntegers L) (a : 𝓞 L) :
    globalAutOfIntegerAut L v w τ • a ∈ w.asIdeal ↔ a ∈ w.asIdeal := by
  have hmem (b : 𝓞 L) : b ∈ w.asIdeal ↔
      algebraMap (𝓞 L) (w.adicCompletionIntegers L) b ∈
        IsLocalRing.maximalIdeal (w.adicCompletionIntegers L) := by
    rw [← under_maximalIdeal_adicCompletionIntegers (K := L) w, Ideal.mem_under]
  rw [hmem, globalAutOfIntegerAut_commutes, hmem]
  constructor
  · intro h
    have h' := completedIntegerAut_preserves_maximalIdeal_pow L v w τ.symm 1
      (τ (algebraMap (𝓞 L) (w.adicCompletionIntegers L) a)) (by simpa using h)
    simpa using h'
  · intro h
    simpa using completedIntegerAut_preserves_maximalIdeal_pow L v w τ 1
      (algebraMap (𝓞 L) (w.adicCompletionIntegers L) a) (by simpa using h)

/-- The restriction belongs to the actual global decomposition group. -/
theorem globalAutOfIntegerAut_mem_stabilizer
    (τ : w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ]
      w.adicCompletionIntegers L) :
    globalAutOfIntegerAut L v w τ ∈ decompositionGroup L w := by
  rw [MulAction.mem_stabilizer_iff, Ideal.pointwise_smul_def]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (globalAutOfIntegerAut_mem_prime_iff L v w τ a).mpr ha
  · intro a ha
    have hinv : (globalAutOfIntegerAut L v w τ)⁻¹ • a ∈ w.asIdeal :=
      (globalAutOfIntegerAut_mem_prime_iff L v w τ _).mp (by simpa using ha)
    simpa using Ideal.mem_map_of_mem
      (MulSemiringAction.toRingHom Gal(L/ℚ) (𝓞 L) (globalAutOfIntegerAut L v w τ)) hinv

/-- Every actual completed-integer automorphism is induced by a global decomposition automorphism.
Normality is proved by the Galois hypothesis in T20; it is not imposed on T21's different bound. -/
theorem decompositionIntegersHom_surjective : Function.Surjective (decompositionIntegersHom L v w) := by
  intro τ
  let σ : decompositionGroup L w :=
    ⟨globalAutOfIntegerAut L v w τ, globalAutOfIntegerAut_mem_stabilizer L v w τ⟩
  refine ⟨σ, ?_⟩
  have hfield : decompositionFieldHom L v w σ = fractionAutOfIntegerAut L v w τ := by
    apply DFunLike.coe_injective
    apply (w.denseRange_algebraMap L).equalizer
      (continuous_completionDecompositionRingEquiv L w σ)
      (continuous_fractionAutOfIntegerAut L v w τ)
    funext x
    change completionDecompositionRingEquiv L w σ (algebraMap L (w.adicCompletion L) x) =
      fractionAutOfIntegerAut L v w τ (algebraMap L (w.adicCompletion L) x)
    rw [completionDecompositionRingEquiv_algebraMap]
    exact AlgEquiv.restrictNormal_commutes
      ((fractionAutOfIntegerAut L v w τ).restrictScalars ℚ) L x
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  change decompositionFieldHom L v w σ
    (algebraMap (w.adicCompletionIntegers L) (w.adicCompletion L) x) = _
  rw [hfield, fractionAutOfIntegerAut_algebraMap]
  rfl

/-- The genuine decomposition group is the automorphism group of the actual completed integer
extension. This equivalence carries the named action, not merely its cardinality. -/
def decompositionIntegersMulEquiv : decompositionGroup L w ≃*
    (w.adicCompletionIntegers L ≃ₐ[v.adicCompletionIntegers ℚ] w.adicCompletionIntegers L) :=
  MulEquiv.ofBijective (decompositionIntegersHom L v w)
    ⟨decompositionIntegersHom_injective L v w, decompositionIntegersHom_surjective L v w⟩

/-- The group equivalence has exactly the constructed completion action as its function. -/
theorem decompositionIntegersMulEquiv_apply (σ : decompositionGroup L w) :
    decompositionIntegersMulEquiv L v w σ = decompositionIntegersHom L v w σ := rfl

end GlobalDifferentTransport
