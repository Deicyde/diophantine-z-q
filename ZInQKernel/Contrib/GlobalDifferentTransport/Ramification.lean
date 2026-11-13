/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Canonical completion-map ingredients are selected from TauCeti revision
 a6027b1d24fcb935c53bd5b50d11b40991cda418.
The equality of Mathlib's concrete integer-ring ramification indices below is
proved from the ideal-map square and all-power multiplicity transport; it does
not import the TauCeti local-field ramification-index wrapper.
-/
module

public import ZInQKernel.Contrib.GlobalDifferentTransport.Extension

/-!
# The actual completed-ring ramification index

All algebra structures come from the canonical continuous field map and its
integer-ring restriction. Thus the local ramification index is the same as the
global one, without a Galois assumption or a finite-module assertion about
localizing at one of several primes above the base prime.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped GlobalDifferentTransportCompletion

namespace GlobalDifferentTransport

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  [Module.IsTorsionFree R B]
  (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

/-- The canonical completed integer-ring algebra map is exactly the restricted field map. -/
theorem algebraMap_completionIntegersAlgebra :
    algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      completionIntegersRingHom K L v w :=
  RingHom.algebraMap_toAlgebra _

/-- The canonical completed field algebra map is the continuous extension of the global one. -/
theorem algebraMap_completionAlgebra :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) = completionRingHom K L v w :=
  RingHom.algebraMap_toAlgebra _

/-- Faithfulness of the canonical completed integer-ring extension. -/
theorem faithfulSMul_completionIntegers :
    FaithfulSMul (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  rw [faithfulSMul_iff_algebraMap_injective, algebraMap_completionIntegersAlgebra]
  exact completionIntegersRingHom_injective K L v w

/-- Torsion-freeness of the canonical extension follows from its actual injective ring map. -/
theorem isTorsionFree_completionIntegers :
    Module.IsTorsionFree (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  let := faithfulSMul_completionIntegers K L v w
  infer_instance

/-- The target completed maximal ideal lies over the source completed maximal ideal. -/
theorem maximalIdeal_completionIntegers_liesOver :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).LiesOver
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  rw [Ideal.liesOver_iff, Ideal.under_def, algebraMap_completionIntegersAlgebra]
  exact (comap_maximalIdeal_completionIntegersRingHom K L v w).symm

/-- The ramification index of the actual completed integer-ring extension is the global index.
The proof computes the local image ideal using the canonical square, then transports its
multiplicity through completion at `w`. -/
theorem ramificationIdx_completionIntegers_eq :
    (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)).ramificationIdx
        (v.adicCompletionIntegers K) = w.asIdeal.ramificationIdx R := by
  let := faithfulSMul_completionIntegers K L v w
  let := isTorsionFree_completionIntegers K L v w
  let := maximalIdeal_completionIntegers_liesOver K L v w
  have hbase : IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field (v.adicCompletionIntegers K)
  have hglobal : v.asIdeal.map (algebraMap R B) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot v.ne_bot
  have hlocal : (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).map
      (algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hbase
  rw [Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (IsLocalRing.maximalIdeal (w.adicCompletionIntegers L)) hlocal,
    algebraMap_completionIntegersAlgebra, map_maximalIdeal_completionIntegersRingHom,
    multiplicity_map_adicCompletionIntegers (K := L) w _ hglobal]
  exact (Ideal.IsDedekindDomain.ramificationIdx_eq_multiplicity
    v.asIdeal w.asIdeal hglobal).symm

/-- The field containing the completed target is an algebra over the completed base integers
through the actual continuous field map. -/
@[reducible]
def completionIntegersToFieldAlgebra :
    Algebra (v.adicCompletionIntegers K) (w.adicCompletion L) :=
  ((completionRingHom K L v w).comp
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).toAlgebra

scoped[GlobalDifferentTransportCompletion] attribute [instance 50]
  GlobalDifferentTransport.completionIntegersToFieldAlgebra

/-- The completed base integers, completed base field, and completed target field form the
canonical scalar tower. -/
theorem completionIntegersFieldIsScalarTower :
    IsScalarTower (v.adicCompletionIntegers K) (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun _ ↦ rfl

/-- The completed base integers, completed target integers, and completed target field form the
same canonical scalar tower. -/
theorem completionIntegersIsScalarTower :
    IsScalarTower (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
      (w.adicCompletion L) :=
  .of_algebraMap_eq fun _ ↦ rfl

/-- The original base field, its completion, and the target completion form a scalar tower. -/
theorem completionFieldIsScalarTower :
    IsScalarTower K (v.adicCompletion K) (w.adicCompletion L) :=
  .of_algebraMap_eq fun x ↦ by
    rw [algebraMap_completionAlgebra]
    change algebraMap L (w.adicCompletion L) (algebraMap K L x) =
      completionRingHom K L v w (algebraMap K (v.adicCompletion K) x)
    symm
    exact completionRingHom_coe K L v w x

/-- The completed-field scalar action is continuous for the canonical algebra. -/
theorem completionFieldContinuousSMul :
    ContinuousSMul (v.adicCompletion K) (w.adicCompletion L) := by
  apply continuousSMul_of_algebraMap
  rw [algebraMap_completionAlgebra]
  exact continuous_completionRingHom K L v w

scoped[GlobalDifferentTransportCompletion] attribute [instance]
  GlobalDifferentTransport.completionIntegersFieldIsScalarTower
  GlobalDifferentTransport.completionIntegersIsScalarTower
  GlobalDifferentTransport.completionFieldIsScalarTower
  GlobalDifferentTransport.completionFieldContinuousSMul
  GlobalDifferentTransport.faithfulSMul_completionIntegers
  GlobalDifferentTransport.isTorsionFree_completionIntegers
  GlobalDifferentTransport.maximalIdeal_completionIntegers_liesOver

end GlobalDifferentTransport
