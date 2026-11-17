/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/AdicCompletionExtension.lean
Original SHA-256: cb885bb9db0121bd63d34b7934962efbf5523e7a4360bf8c54b55013a1227529
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
TauCeti/RingTheory/DedekindDomain/AdicCompletionExtension.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


/-
## Provenance

Adapted, with the authors' proofs, from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0, pinned by
`TauCetiRoadmap/EllipticCurves/README.md` at `66889eada51a`),
`EllipticCurves/Mathlib/AdicCompletionExtension.lean`.

That file in turn credits the FLT project
(`github.com/ImperialCollegeLondon/FLT`, `FLT/DedekindDomain/Completion/BaseChange.lean`, by
Kevin Buzzard, Andrew Yang and Matthew Jasper) for the completion-extension material, rebased
there onto Mathlib's `valuation_liesOver` and `uniformContinuous_algebraMap_liesOver`; the same
rebasing is used here, so both are credited.

`span_singleton_eq_maximalIdeal_pow` comes from that same Stoll file, restated here against this
repository's `HeightOneSpectrum` interface.

`exists_unit_not_isSquare` comes from the same source file (`:183`). Two deliberate departures from
its proof: the source contracts the maximal ideal with its own
`comap_maximalIdeal_adicCompletionIntegers`, which this repository states as
`under_maximalIdeal_adicCompletionIntegers` (`Ideal.under R I` is by definition
`I.comap (algebraMap R S)`); and where the source derives `v d = 1` from a square by manipulating
`WithZero.log`, this uses Mathlib's `mul_self_le_one_iff` and `one_le_mul_self_iff`, which say the
same thing about the ordered value monoid in one line. The odd-residue-characteristic step is split
out as `ringChar_residueField_adicCompletionIntegers_ne_two`, which the source keeps inline.

The Henselian and completeness chain from that same Stoll file lives in
`TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion`, with the single-completion
valuation and residue-field results it rests on — among them
`residueFieldEquivAdicCompletionIntegers`, which this file uses.
-/

import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.Completion
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.Ideal
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Radical.Basic
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

noncomputable section

section

open IsDedekindDomain WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/- The valuation associated to the maximal ideal of the ring of integers of an adic completion is
the valuation of the completion.

This is what lets a condition stated at the height-one primes of `𝒪_v` be read as a condition on
`K_v`: `𝒪_v` is a discrete valuation ring, so it has exactly one, and it induces `Valued.v`.

Not `@[simp]`: this is the special case `P = IsDiscreteValuationRing.maximalIdeal _` of
`valuation_adicCompletionIntegers`, which carries the annotation instead. With both marked, the
`simpNF` linter rejects this one — "simp can prove this" — because the general form subsumes it. -/
end IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain.HeightOneSpectrum

section Extension

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]

variable (K L)

/- The extension of adic completions along `w ∣ v`: the ring homomorphism `K_v →+* L_w`
continuously extending `K → L`. -/
noncomputable def adicCompletionExtension : v.adicCompletion K →+* w.adicCompletion L :=
  haveI : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  (adicCompletion.equiv L w).symm.toRingHom.comp <|
    (UniformSpace.Completion.mapRingHom
      (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L)))
      (uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w).continuous).comp
      (adicCompletion.equiv K v).toRingHom

/- The algebra structure on `L_w` over `K_v` induced by `adicCompletionExtension`, available in
the `AdicCompletionExtension` scope. -/
@[reducible]
noncomputable def adicCompletionExtensionAlgebra :
    Algebra (v.adicCompletion K) (w.adicCompletion L) :=
  (adicCompletionExtension K L v w).toAlgebra

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletionExtensionAlgebra

open scoped AdicCompletionExtension

/- The algebra map of `adicCompletionExtensionAlgebra` is `adicCompletionExtension`. -/
@[simp]
theorem algebraMap_adicCompletionExtensionAlgebra :
    algebraMap (v.adicCompletion K) (w.adicCompletion L) =
      adicCompletionExtension K L v w :=
  RingHom.algebraMap_toAlgebra _

/- Under `toCompletion`, the image of `x` is `UniformSpace.Completion.map` of the algebra map
applied to `x.toCompletion`. -/
@[simp]
lemma toCompletion_adicCompletionExtension (x : v.adicCompletion K) :
    (adicCompletionExtension K L v w x).toCompletion =
      UniformSpace.Completion.map
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) x.toCompletion :=
  (rfl)

/- The square with sides `K → K_v → L_w` and `K → L → L_w` commutes. -/
-- Not `@[simp]`: the `simpNF` linter rejects it, because `simp` rewrites the left-hand side
-- further through `WithVal.equiv_symm_apply`, so this is not in simp normal form.
lemma adicCompletionExtension_coe (x : K) :
    adicCompletionExtension K L v w (x : v.adicCompletion K) =
      (algebraMap K L x : w.adicCompletion L) := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  apply adicCompletion.ext
  rw [toCompletion_adicCompletionExtension, adicCompletion.coe_toCompletion,
    UniformSpace.Completion.map_coe
      (uniformContinuous_algebraMap_liesOver (K := K) (L := L) v w)]
  -- `WithVal` is a type synonym, so `algebraMap (WithVal _) (WithVal _)` is `algebraMap K L`
  -- transported along it; these two rewrites name that identification rather than leaving it to
  -- a bare `rfl`.
  rw [WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply]

/- The square with sides `R → K_v → L_w` and `R → B → L_w` commutes. -/
@[simp]
lemma adicCompletionExtension_algebraMap (a : R) :
    adicCompletionExtension K L v w (algebraMap R (v.adicCompletion K) a) =
      algebraMap B (w.adicCompletion L) (algebraMap R B a) := by
  rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K)]
  simp only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, adicCompletionExtension_coe, ← IsScalarTower.algebraMap_apply R K L,
    ← IsScalarTower.algebraMap_apply R B L]

/- `adicCompletionExtension` is continuous. -/
theorem continuous_adicCompletionExtension :
    Continuous (adicCompletionExtension K L v w) := by
  have h : (adicCompletionExtension K L v w : v.adicCompletion K → w.adicCompletion L) =
      adicCompletion.ofCompletion ∘ UniformSpace.Completion.map
        (algebraMap (WithVal (v.valuation K)) (WithVal (w.valuation L))) ∘
        adicCompletion.toCompletion := by
    funext x
    rw [Function.comp_apply, Function.comp_apply, ← toCompletion_adicCompletionExtension,
      adicCompletion.ofCompletion_toCompletion]
  rw [h]
  exact (adicCompletion.continuous_ofCompletion L w).comp
    (UniformSpace.Completion.continuous_map.comp (adicCompletion.continuous_toCompletion K v))

/- `adicCompletionExtension` is the *only* continuous ring homomorphism `K_v →+* L_w` extending
`K → L`: `K` is dense in `K_v`, so a continuous map out of it is pinned by its values there.

This is the universal property, available without unfolding the definition. -/
theorem eq_adicCompletionExtension_of_continuous {f : v.adicCompletion K →+* w.adicCompletion L}
    (hf : Continuous f)
    (hfK : ∀ x : K, f (x : v.adicCompletion K) = (algebraMap K L x : w.adicCompletion L)) :
    f = adicCompletionExtension K L v w :=
  DFunLike.coe_injective <| (v.denseRange_algebraMap K).equalizer hf
    (continuous_adicCompletionExtension K L v w)
    (funext fun x ↦ by
      simp only [Function.comp_apply, algebraMap_adicCompletion, Algebra.algebraMap_self_apply]
      rw [hfK x, adicCompletionExtension_coe])

open WithZeroTopology in
/- The valuation on `L_w` restricted along `K_v → L_w` is the valuation on `K_v` raised to the
ramification index of `w` over `v`. -/
@[simp]
lemma valued_adicCompletionExtension (x : v.adicCompletion K) :
    Valued.v (adicCompletionExtension K L v w x) =
      Valued.v x ^ v.asIdeal.ramificationIdx' w.asIdeal := by
  have : FaithfulSMul R B := FaithfulSMul.of_field_isFractionRing R B K L
  rw [← adicCompletion.valued_toCompletion L w (adicCompletionExtension K L v w x),
    toCompletion_adicCompletionExtension, ← adicCompletion.valued_toCompletion K v x]
  have hsurjK : Function.Surjective (⇑(Valued.v : Valuation (v.valuation K).Completion ℤᵐ⁰)) :=
    Valued.valuedCompletion_surjective_iff.mpr <| .of_comp (v.valuation_surjective K)
  have hsurjL : Function.Surjective (⇑(Valued.v : Valuation (w.valuation L).Completion ℤᵐ⁰)) :=
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
  -- Mathlib's `valuation_liesOver` states the exponent as `w.asIdeal.ramificationIdx R`, which
  -- `ramificationIdx'_eq_ramificationIdx` identifies with the `ramificationIdx'` used here.
  rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot]
  exact valuation_liesOver (K := K) L v w (WithVal.equiv (v.valuation K) a)

/- The extension maps the ring of integers of `K_v` into the ring of integers of `L_w`. -/
@[simp]
lemma adicCompletionExtension_mem_adicCompletionIntegers (x : v.adicCompletionIntegers K) :
    adicCompletionExtension K L v w (x : v.adicCompletion K) ∈ w.adicCompletionIntegers L := by
  rw [mem_adicCompletionIntegers, valued_adicCompletionExtension]
  exact pow_le_one' ((mem_adicCompletionIntegers ..).mp x.2) _

/- The restriction of `adicCompletionExtension` to the rings of integers. -/
noncomputable def adicCompletionIntegersExtension :
    v.adicCompletionIntegers K →+* w.adicCompletionIntegers L :=
  ((adicCompletionExtension K L v w).comp
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K))).codRestrict
      (w.adicCompletionIntegers L).toSubring
      fun x ↦ adicCompletionExtension_mem_adicCompletionIntegers K L v w x

/- `adicCompletionIntegersExtension` agrees with `adicCompletionExtension` on the integers. -/
@[simp]
lemma coe_adicCompletionIntegersExtension (x : v.adicCompletionIntegers K) :
    (adicCompletionIntegersExtension K L v w x : w.adicCompletion L) =
      adicCompletionExtension K L v w (x : v.adicCompletion K) :=
  (rfl)

/- The maximal ideal of the ring of integers of `L_w` contracts to the maximal ideal of the ring
of integers of `K_v`.

Stated with `Ideal.comap` of the explicit ring homomorphism, not `Ideal.under`: `Ideal.under A` is
`Ideal.comap (algebraMap A B)` and so needs an `Algebra (v.adicCompletionIntegers K)
(w.adicCompletionIntegers L)` instance, which is only installed in the `AdicCompletionExtension`
scope. The `Ideal.LiesOver` form for that scoped algebra is
`maximalIdeal_adicCompletionIntegers_liesOver`. -/
end Extension

end IsDedekindDomain.HeightOneSpectrum

open Polynomial

namespace AdjoinRoot

/- The base-change map `K[X] ⧸ (p) →+* K_v[X] ⧸ (q)` of `AdjoinRoot`s at a completion is
compatible with the algebra maps from the underlying Dedekind domain `R` and from the ring of
integers of the completion. -/
-- Lives here rather than beside `AdjoinRoot.map` in `TauCeti.RingTheory.AdjoinRoot.Factors`
-- because it is not a fact about `AdjoinRoot` alone: it names `adicCompletion` and
-- `adicCompletionIntegers`, and this module is where those two developments first meet.
end AdjoinRoot

end
