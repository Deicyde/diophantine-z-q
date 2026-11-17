/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/RingTheory/DedekindDomain/AdicValuation/IntegralClosure.lean
Original SHA-256: 1abac2232276952f95fa5671228344019aa9500252f62700a444d8257fb09d87
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
TauCeti/RingTheory/DedekindDomain/AdicValuation/IntegralClosure.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.FiniteExtension.Basic
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.IntegerRing
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.IntegersExtension
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.DedekindDomain.AdicValuation.ValuativeExtension
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open IsDedekindDomain ValuativeRel
open scoped AdicCompletionExtension

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  {L : Type*} [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsFractionRing B L] [IsScalarTower R B L]
  (v : HeightOneSpectrum R) (w : HeightOneSpectrum B) [w.asIdeal.LiesOver v.asIdeal]
  [Finite (R ⧸ v.asIdeal)] [Finite (B ⧸ w.asIdeal)]

variable (K L)

/- **A completion of an extension is a finite extension of completions.** For the canonical
algebra structure of `adicCompletionExtension`, `L_w` is a finite `K_v`-module. Mathlib's
instance for an adic completion assumes that `K` and `L` are number fields and holds for an
arbitrary compatible algebra structure; this one is about the canonical structure over an
arbitrary Dedekind base. -/
theorem adicCompletion_moduleFinite :
    Module.Finite (v.adicCompletion K) (w.adicCompletion L) :=
  TauCeti.finite_of_valuativeExtension _ _

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletion_moduleFinite

/- **`𝒪_w` is the integral closure of `𝒪_v` in `L_w`.** An element of `L_w` is integral over
`𝒪_v` exactly when its valuation is at most `1`, because the valuation of `L_w` is the unique
extension of the valuation of `K_v`. -/
theorem adicCompletionIntegers_isIntegralClosure :
    IsIntegralClosure (w.adicCompletionIntegers L) (v.adicCompletionIntegers K)
      (w.adicCompletion L) where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff := by
    intro x
    rw [Valuation.Integers.isIntegral_iff_valuation_le_one
        (v.valuation_integers_adicCompletionIntegers (K := K)) x,
      ← w.mem_adicCompletionIntegers_iff_valuation_le_one (K := L) x]
    exact ⟨fun h ↦ ⟨⟨x, h⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.2⟩

scoped[AdicCompletionExtension] attribute [instance]
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers_isIntegralClosure

omit [Finite (R ⧸ v.asIdeal)] [Finite (B ⧸ w.asIdeal)] in
/- **The identifications of the integer rings are natural.** The identifications
`𝒪[K_v] = 𝒪_v` and `𝒪[L_w] = 𝒪_w` commute with the map `𝒪[K_v] → 𝒪[L_w]` of the valuative
extension and the map `𝒪_v → 𝒪_w` of `adicCompletionIntegersExtension`, both of which are
restrictions of the canonical map `K_v → L_w`. -/
@[simp]
theorem integerEquivAdicCompletionIntegers_algebraMap (x : 𝒪[v.adicCompletion K]) :
    w.integerEquivAdicCompletionIntegers (K := L)
        (algebraMap 𝒪[v.adicCompletion K] 𝒪[w.adicCompletion L] x) =
      algebraMap (v.adicCompletionIntegers K) (w.adicCompletionIntegers L)
        (v.integerEquivAdicCompletionIntegers (K := K) x) :=
  Subtype.val_injective <| by
    simp


/- **`𝒪_w` is a lattice of full rank in `L_w`.** Its rank as an `𝒪_v`-module is the degree
`[L_w : K_v]` of the local extension. -/
end IsDedekindDomain.HeightOneSpectrum

end

end
