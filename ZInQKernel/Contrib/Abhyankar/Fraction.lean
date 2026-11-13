/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Authors: The Tau Ceti contributors, Chris Birkbeck

Modified for this contribution: minimal port to Mathlib v4.35.0 and a project
namespace of `isFractionRing_algebra_adjoin_of_adjoin_eq_top` from
TauCeti/FieldTheory/IntermediateField/Adjoin/EqTop.lean,
revision 30f41378f0cb1d569f51d8a4d0cb74aea8a80e44.
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Finiteness

/-!
# The actual fraction field of a generated integral model

Field generation over `Frac(R)` is connected to the fraction field of the
`R`-subalgebra by explicit denominator clearing. No power-basis or
normalization identification is assumed.
-/

namespace ZInQ.Contrib.Abhyankar

/-- If a set generates `M` over the specified fraction field of `R`, then its
`R`-adjoin has fraction field `M`, with the given embeddings. -/
theorem isFractionRing_adjoin_of_adjoin_eq_top
    {R K M : Type*} [CommRing R] [Field K] [Field M]
    [Algebra R K] [IsFractionRing R K] [Algebra R M] [Algebra K M]
    [IsScalarTower R K M] {s : Set M} (h : IntermediateField.adjoin K s = ⊤) :
    IsFractionRing (Algebra.adjoin R s) M := by
  have hinj : Function.Injective (algebraMap R M) := by
    rw [IsScalarTower.algebraMap_eq R K M]
    exact (algebraMap K M).injective.comp (IsFractionRing.injective R K)
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  have hz : z ∈ IntermediateField.adjoin K s := h ▸ trivial
  obtain ⟨r, hr, u, hu, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hz
  obtain ⟨⟨a, ha⟩, har⟩ := multiple_mem_adjoin_of_mem_localization_adjoin
    (nonZeroDivisors R) K s r hr
  obtain ⟨⟨b, hb⟩, hbu⟩ := multiple_mem_adjoin_of_mem_localization_adjoin
    (nonZeroDivisors R) K s u hu
  have : Nontrivial R := (algebraMap R K).domain_nontrivial
  have ha0 : algebraMap R M a ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha)
  have hb0 : algebraMap R M b ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hb)
  refine ⟨algebraMap R _ b * ⟨_, har⟩, algebraMap R _ a * ⟨_, hbu⟩, ?_⟩
  simp only [map_mul, ← IsScalarTower.algebraMap_apply, Subalgebra.algebraMap_apply,
    Submonoid.smul_def, Algebra.smul_def]
  rw [mul_left_comm (algebraMap R M a), mul_div_mul_left _ _ hb0, mul_div_mul_left _ _ ha0]

end ZInQ.Contrib.Abhyankar
