/-
Ported with Codex assistance on 2026-11-14 from trureturing@8af78b5bb176c99b2750222c0dd3d00a475d39eb.
Source: D5/S3/Factorization/Dedekind/HilbertDifferent/NumberTheory/LocalField/RamificationGroup.lean
Original SHA-256: e7083da89450d27ef62cc02f90da225ba379f14aa02cd75fdd0ecd7e8b03abf9
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
TauCeti/NumberTheory/LocalField/RamificationGroup.lean.
Full license and pertinent inherited attribution: ZInQKernel/Contrib/HilbertDifferent/Attribution.lean.
Replace this port by direct use when this project's pinned Mathlib supplies an equivalent declaration. -/


import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.GaloisAction
import ZInQKernel.Contrib.HilbertDifferent.NumberTheory.LocalField.RamificationIndex
import ZInQKernel.Contrib.HilbertDifferent.RingTheory.LocalRing.RamificationGroup
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Localization.Basic
import ZInQKernel.Contrib.HilbertDifferent.Support.TameDifferent

noncomputable section

section
noncomputable section

open ValuativeRel

namespace TauCeti.LocalFieldsRamification

/- The interval `[-1, ∞)`, the domain of the Herbrand function and of its inverse. The lower
ramification groups are indexed by real numbers `u ≥ -1`, and `G_u` is the whole automorphism
group for `u ≤ -1`. -/
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L]

/- The lower-numbering ramification group of a finite extension of local fields. -/
def lowerRamificationGroup (i : ℤ) : Subgroup (L ≃ₐ[K] L) :=
  TauCeti.IsLocalRing.ramificationGroup (L ≃ₐ[K] L) 𝒪[L] i

/- The local-field filtration is the ramification filtration of its integer ring. -/
theorem lowerRamificationGroup_def (i : ℤ) :
    lowerRamificationGroup K L i =
      TauCeti.IsLocalRing.ramificationGroup (L ≃ₐ[K] L) 𝒪[L] i :=
  (rfl)

section Tower

variable (K' : Type*) [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L]
  [ValuativeExtension K' L] [Module.Finite K' L]

end Tower

end TauCeti.LocalFieldsRamification
