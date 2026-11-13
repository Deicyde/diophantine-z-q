/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Selected canonical-completion map proofs adapted to Mathlib v4.35.0 from
TauCeti revision a6027b1d24fcb935c53bd5b50d11b40991cda418,
TauCeti/RingTheory/DedekindDomain/AdicCompletionExtension.lean, lines 269–447.
The scoped algebra structures and ideal-map square are made explicit here.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.Multiplicity
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Canonical algebra maps between completed fields and integer rings

The continuous extension of the actual map of fraction fields induces all
local algebra structures used here. The integer-ring square commutes with the
global affine-model square. No comparison of differents is assumed.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace GlobalDifferentTransport

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  [Module.IsTorsionFree R B]
  (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/-- The canonical continuous extension of the fraction-field embedding. -/
def completionRingHom : v.adicCompletion K →+* w.adicCompletion L :=
  (adicCompletion.equiv L w).symm.toRingHom.comp <|
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom

/-- On the underlying uniform-space completions this is `Completion.map`. -/
theorem toCompletion_completionRingHom (x : v.adicCompletion K) :
    (completionRingHom K L v w x).toCompletion =
      UniformSpace.Completion.map
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) x.toCompletion := rfl

/-- The fraction-field embedding square commutes. -/
theorem completionRingHom_coe (x : K) :
    completionRingHom K L v w (x : v.adicCompletion K) =
      (algebraMap K L x : w.adicCompletion L) := by
  apply adicCompletion.ext
  rw [toCompletion_completionRingHom, adicCompletion.coe_toCompletion,
    UniformSpace.Completion.map_coe
      (uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w),
    WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply]

/-- The affine-model embedding square commutes in the completed fields. -/
theorem completionRingHom_algebraMap (a : R) :
    completionRingHom K L v w (algebraMap R (v.adicCompletion K) a) =
      algebraMap B (w.adicCompletion L) (algebraMap R B a) := by
  rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K)]
  simp only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, completionRingHom_coe, ← IsScalarTower.algebraMap_apply R K L,
    ← IsScalarTower.algebraMap_apply R B L]

/-- Continuity of the canonical completion map. -/
theorem continuous_completionRingHom : Continuous (completionRingHom K L v w) := by
  have h : (completionRingHom K L v w : v.adicCompletion K → w.adicCompletion L) =
      adicCompletion.ofCompletion ∘ UniformSpace.Completion.map
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) ∘
        adicCompletion.toCompletion := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, ← toCompletion_completionRingHom,
      adicCompletion.ofCompletion_toCompletion]
  rw [h]
  exact (adicCompletion.continuous_ofCompletion L w).comp
    (UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v))

/-- The map is determined by continuity and its values on the global fraction field. -/
theorem eq_completionRingHom_of_continuous
    {f : v.adicCompletion K →+* w.adicCompletion L} (hf : Continuous f)
    (hfK : ∀ x : K, f (x : v.adicCompletion K) = (algebraMap K L x : w.adicCompletion L)) :
    f = completionRingHom K L v w :=
  DFunLike.coe_injective <| (v.denseRange_algebraMap K).equalizer hf
    (continuous_completionRingHom K L v w)
    (funext fun x ↦ by
      simp only [Function.comp_apply, algebraMap_adicCompletion, Algebra.algebraMap_self_apply]
      rw [hfK x, completionRingHom_coe])

open WithZeroTopology in
/-- The normalized completed valuation restricts by the genuine global ramification index. -/
theorem valued_completionRingHom (x : v.adicCompletion K) :
    Valued.v (completionRingHom K L v w x) =
      Valued.v x ^ w.asIdeal.ramificationIdx R := by
  rw [← adicCompletion.valued_toCompletion_apply L w (completionRingHom K L v w x),
    toCompletion_completionRingHom, ← adicCompletion.valued_toCompletion_apply K v x]
  have hsurjK : Function.Surjective
      (Valued.v : (v.valuation K).Completion → ℤᵐ⁰) :=
    Valued.valuedCompletion_surjective_iff.mpr <| .of_comp (v.valuation_surjective K)
  have hsurjL : Function.Surjective
      (Valued.v : (w.valuation L).Completion → ℤᵐ⁰) :=
    Valued.valuedCompletion_surjective_iff.mpr <| .of_comp (w.valuation_surjective L)
  generalize x.toCompletion = y
  revert y
  apply funext_iff.mp
  symm
  apply UniformSpace.Completion.ext
  · exact (Valued.continuous_valuation_of_surjective hsurjK).pow _
  · exact (Valued.continuous_valuation_of_surjective hsurjL).comp
      UniformSpace.Completion.continuous_map
  intro a
  rw [UniformSpace.Completion.map_coe
    (uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w),
    Valued.valuedCompletion_apply, Valued.valuedCompletion_apply]
  exact valuation_liesOver (K := K) L v w (WithVal.equiv (v.valuation K) a)

/-- The canonical map takes completed integers to completed integers. -/
theorem completionRingHom_mem_integers (x : v.adicCompletionIntegers K) :
    completionRingHom K L v w (x : v.adicCompletion K) ∈ w.adicCompletionIntegers L := by
  rw [mem_adicCompletionIntegers, valued_completionRingHom]
  exact pow_le_one' ((mem_adicCompletionIntegers ..).mp x.2) _

/-- Restriction of the canonical completion map to the concrete integer rings. -/
def completionIntegersRingHom : v.adicCompletionIntegers K →+* w.adicCompletionIntegers L :=
  ((completionRingHom K L v w).comp
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).codRestrict
      (w.adicCompletionIntegers L).toSubring
      fun x ↦ completionRingHom_mem_integers K L v w x

/-- Restriction to integer rings does not change the ambient field map. -/
theorem coe_completionIntegersRingHom (x : v.adicCompletionIntegers K) :
    (completionIntegersRingHom K L v w x : w.adicCompletion L) =
      completionRingHom K L v w (x : v.adicCompletion K) := rfl

/-- The canonical affine-model square commutes in the completed integer rings. -/
theorem completionIntegersRingHom_algebraMap (a : R) :
    completionIntegersRingHom K L v w (algebraMap R (v.adicCompletionIntegers K) a) =
      algebraMap B (w.adicCompletionIntegers L) (algebraMap R B a) := by
  apply Subtype.ext
  change completionRingHom K L v w (algebraMap R (v.adicCompletion K) a) =
    algebraMap B (w.adicCompletion L) (algebraMap R B a)
  exact completionRingHom_algebraMap K L v w a

/-- The integer-ring restriction is injective, because the completed fraction-field map is. -/
theorem completionIntegersRingHom_injective :
    Function.Injective (completionIntegersRingHom K L v w) := by
  intro x y h
  apply Subtype.ext
  apply (completionRingHom K L v w).injective
  exact congrArg (fun z : w.adicCompletionIntegers L ↦ (z : w.adicCompletion L)) h

/-- The completed maximal ideal lies over the completed base maximal ideal under the
actual restricted map. This uses positivity of the global ramification index. -/
theorem comap_maximalIdeal_completionIntegersRingHom :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).comap
        (completionIntegersRingHom K L v w) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  ext x
  rw [Ideal.mem_comap]
  refine (Valuation.mem_maximalIdeal_iff
    (v := (Valued.v : Valuation (w.adicCompletion L) ℤᵐ⁰))).trans <| Iff.trans ?_
    (Valuation.mem_maximalIdeal_iff
      (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰))).symm
  rw [coe_completionIntegersRingHom K L v w, valued_completionRingHom]
  exact pow_lt_one_iff
    (Ideal.ramificationIdx_pos_of_isDedekindDomain' w.asIdeal v.ne_bot).ne'

/-- The image of the completed base maximal ideal is the extension of the genuine
mapped global base prime. This is an ideal identity, not just a valuation convention. -/
theorem map_maximalIdeal_completionIntegersRingHom :
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).map
        (completionIntegersRingHom K L v w) =
      (v.asIdeal.map (algebraMap R B)).map
        (algebraMap B (w.adicCompletionIntegers L)) := by
  rw [← map_asIdeal_adicCompletionIntegers (K := K) v, Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro a
  exact completionIntegersRingHom_algebraMap K L v w a

/-- The algebra structure on completed fields is induced by the canonical completion map. -/
@[reducible]
def completionAlgebra : Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (completionRingHom K L v w).toAlgebra

/-- The algebra structure on completed integer rings is induced by its canonical restriction. -/
@[reducible]
def completionIntegersAlgebra :
    Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  (completionIntegersRingHom K L v w).toAlgebra

scoped[GlobalDifferentTransportCompletion] attribute [instance 50]
  GlobalDifferentTransport.completionAlgebra GlobalDifferentTransport.completionIntegersAlgebra

end GlobalDifferentTransport
