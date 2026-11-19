import ActualFiniteRamificationV002
import NumberFieldResiduePrimeAlgebraic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The actual strict-displacement group is pro-residue-characteristic

A continuous discrete quotient has an open kernel in the actual subgroup
Krull topology. A genuine finite Galois fixing subgroup is contained in
that kernel. Its actual strict-displacement image is a residue-prime
group, so the continuous quotient is one too. No pro-p model is an input.
-/

noncomputable section
set_option autoImplicit false

namespace ActualWildProPrime

open Topology Filter

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
variable [CharZero K] [IsAlgClosure K Ω]

/-- Every continuous discrete quotient of the literal wild group is a
p-group for its actual residue characteristic. -/
theorem continuous_wild_discrete_image_isPGroup (w : ValuationSubring Ω) (p : ℕ)
    [Fact p.Prime] [CharP (IsLocalRing.ResidueField w) p]
    {H : Type*} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    (f : WildFiniteGroup.strictDisplacementGroup (K := K) w →* H) (hf : Continuous f) :
    IsPGroup p f.range := by
  let W := WildFiniteGroup.strictDisplacementGroup (K := K) w
  have hsing : ({1} : Set H) ∈ 𝓝 (f 1) := by
    rw [map_one]
    exact (isOpen_discrete {1}).mem_nhds (Set.mem_singleton 1)
  have hker := hf.continuousAt.preimage_mem_nhds hsing
  rw [nhds_subtype (W : Set (Ω ≃ₐ[K] Ω)) (1 : W)] at hker
  obtain ⟨U, hU, hsub⟩ := Filter.mem_comap.mp hker
  change U ∈ 𝓝 (1 : Ω ≃ₐ[K] Ω) at hU
  obtain ⟨L, hL⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois U).mp hU
  let r : (Ω ≃ₐ[K] Ω) →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L
  let rW : W →* (L ≃ₐ[K] L) := r.comp W.subtype
  haveI : CharP (IsLocalRing.ResidueField (w.comap L.val.toRingHom)) p :=
    (ValuationResidueCharacteristic.residue_charP_iff w L.val.toRingHom p).mpr inferInstance
  have hR : rW.range ≤ WildFiniteGroup.strictDisplacementGroup (K := K) (w.comap L.val.toRingHom) := by
    rintro tau ⟨sigma, rfl⟩
    exact ActualFiniteRamification.restriction_strict w L sigma.1 sigma.2
  have hP : IsPGroup p rW.range :=
    (WildFiniteGroup.strictDisplacementGroup_isPGroup (w.comap L.val.toRingHom) p).to_le hR
  intro x
  obtain ⟨sigma, hsigma⟩ := x.2
  let y : rW.range := ⟨rW sigma, ⟨sigma, rfl⟩⟩
  obtain ⟨k, hk⟩ := hP y
  have hkVal : rW sigma ^ (p ^ k) = 1 := by
    have h := congrArg (fun z : rW.range => z.1) hk
    exact h
  have hfix : (sigma ^ (p ^ k)).1 ∈ L.fixingSubgroup := by
    rw [FiniteGaloisIntermediateField.mem_fixingSubgroup_iff]
    change rW (sigma ^ (p ^ k)) = 1
    rw [map_pow]
    exact hkVal
  have hmem : sigma ^ (p ^ k) ∈ f ⁻¹' ({1} : Set H) := hsub (hL hfix)
  refine ⟨k, Subtype.ext ?_⟩
  change x.1 ^ (p ^ k) = 1
  rw [← hsigma, ← map_pow]
  exact Set.mem_singleton_iff.mp hmem

/-- The prime and the pro-prime statement are derived on the actual
number-field valuation extension, with no supplied characteristic model. -/
theorem numberField_actual_wild_pro_prime [NumberField K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O] (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) :
    ∃ p : ℕ, p.Prime ∧ CharP (IsLocalRing.ResidueField w) p ∧
      ∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H]
        (f : WildFiniteGroup.strictDisplacementGroup (K := K) w →* H),
        Continuous f → IsPGroup p f.range := by
  obtain ⟨p, hp, hchar⟩ := ValuationResidueCharacteristic.numberField_residue_prime O
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : CharP (IsLocalRing.ResidueField (w.comap (algebraMap K Ω))) p := by rwa [hw]
  haveI : CharP (IsLocalRing.ResidueField w) p :=
    (ValuationResidueCharacteristic.residue_charP_iff w (algebraMap K Ω) p).mp inferInstance
  exact ⟨p, hp, inferInstance, fun H _ _ _ f hf => continuous_wild_discrete_image_isPGroup w p f hf⟩

#check continuous_wild_discrete_image_isPGroup
#print axioms continuous_wild_discrete_image_isPGroup
#check numberField_actual_wild_pro_prime
#print axioms numberField_actual_wild_pro_prime

end ActualWildProPrime
