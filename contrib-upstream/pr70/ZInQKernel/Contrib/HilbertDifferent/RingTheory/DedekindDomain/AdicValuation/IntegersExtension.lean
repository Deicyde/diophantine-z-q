/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/AdicValuation/IntegersExtension.lean
Original SHA-256: 6ada2ac28b7d8bee42704924ae3a6505490baae58e55ce02f1f90206b4307dcb
Changes: contribution import paths and namespace; retained proof content.
Full licenses and provenance: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
-/

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/- Adapted to the repository-pinned Mathlib API; only declarations needed by the
Hilbert different consumer are retained. Source: TauCeti@33c2099c678ea391f7ea3e0ddaf945a76a625e5d,
TauCeti/RingTheory/DedekindDomain/AdicValuation/IntegersExtension.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicCompletionExtension
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open IsDedekindDomain
open scoped AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

section Extension

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

variable (K L)

/- The map `𝒪_v → 𝒪_w` on completed integer rings is injective: it is a restriction of a ring
homomorphism out of the field `K_v`. -/
theorem adicCompletionIntegersExtension_injective :
    Function.Injective (adicCompletionIntegersExtension K L v w) := by
  intro x y h
  apply Subtype.val_injective
  apply (adicCompletionExtension K L v w).injective
  rw [← coe_adicCompletionIntegersExtension, ← coe_adicCompletionIntegersExtension, h]

/- The map `𝒪_v → 𝒪_w` on completed integer rings extends the global map `R → B`. -/
@[simp]
theorem adicCompletionIntegersExtension_algebraMap (r : R) :
    adicCompletionIntegersExtension K L v w (algebraMap R (v.adicCompletionIntegers K) r) =
      algebraMap B (w.adicCompletionIntegers L) (algebraMap R B r) := by
  apply Subtype.val_injective
  rw [coe_adicCompletionIntegersExtension, algebraMap_adicCompletionIntegers_apply,
    algebraMap_adicCompletionIntegers_apply, adicCompletionExtension_coe,
    ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R B L]

/- The algebra structure on `𝒪_w` over `𝒪_v` induced by `adicCompletionIntegersExtension`,
available in the `AdicCompletionExtension` scope. -/
@[reducible]
def adicCompletionIntegersExtensionAlgebra :
    Algebra (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) :=
  (adicCompletionIntegersExtension K L v w).toAlgebra

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegersExtensionAlgebra

/- The algebra map of `adicCompletionIntegersExtensionAlgebra` is
`adicCompletionIntegersExtension`. -/
@[simp]
theorem algebraMap_adicCompletionIntegersExtensionAlgebra :
    algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) =
      adicCompletionIntegersExtension K L v w :=
  RingHom.algebraMap_toAlgebra _

/- The completed integer rings `𝒪_v ⊆ 𝒪_w` and the completion `L_w` form a scalar tower. Here
`𝒪_v` acts on `L_w` through `K_v`, so this says the two ways of letting `𝒪_v` act on `L_w`
agree. -/
theorem adicCompletionIntegers_isScalarTower :
    IsScalarTower (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
      (w.adicCompletion L) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply (v.adicCompletionIntegers K) (v.adicCompletion K),
      algebraMap_adicCompletionExtensionAlgebra, algebraMap_adicCompletionIntegersExtensionAlgebra]
    exact (coe_adicCompletionIntegersExtension K L v w x).symm

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_isScalarTower

/- `𝒪_w` is a torsion-free `𝒪_v`-module. -/
theorem adicCompletionIntegers_isTorsionFree :
    Module.IsTorsionFree (v.adicCompletionIntegers K) (w.adicCompletionIntegers L) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective,
    algebraMap_adicCompletionIntegersExtensionAlgebra]
  exact adicCompletionIntegersExtension_injective K L v w

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_isTorsionFree

/- The canonical map `𝒪_v → 𝒪_w` of completed integer rings is a local ring homomorphism. -/

/- The maximal ideal of `𝒪_w` lies over the maximal ideal of `𝒪_v`. -/

end Extension

end IsDedekindDomain.HeightOneSpectrum
