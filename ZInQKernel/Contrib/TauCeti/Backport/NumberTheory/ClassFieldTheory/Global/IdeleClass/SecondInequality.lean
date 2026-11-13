/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SecondInequality), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SecondInequality`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.SecondInequality
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Index
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.IdeleClass.FirstInequality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.ClassField
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.CoprimeNorm
import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.PrimeDegree

public section
noncomputable section

section
open IntermediateField NumberField
namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]
  (h : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [IsGalois F L] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p],
    Module.finrank F L = p → (GlobalNumberFields.ideleClassNormMap F L).range.index ≤ p)

/-- **`H¹` of the global idele-class formation vanishes.** For every finite normal layer
`V ◁ U` of `G_K`, the group `H¹(U/V, C_L)` is trivial. -/
theorem subsingleton_h1_globalFormation
    (Lay : NormalLayer (AbsoluteGaloisGroup K)) :
    Subsingleton (Lay.H (globalFormation K) 1) :=
  subsingleton_h1_globalFormation_of_forall_index_le
    (fun F L _ _ _ _ _ _ p _ _ hfin ↦
      index_range_ideleClassNormMap_le_of_finrank_prime F L p hfin) Lay

end TauCeti.ClassFieldTheory
end

section
open IntermediateField NumberField
namespace TauCeti.ClassFieldTheory

variable {K : Type} [Field K] [NumberField K]
  (h : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
    [IsGalois F L] (p : ℕ) [Fact p.Prime] [HasEnoughRootsOfUnity F p],
    Module.finrank F L = p → (GlobalNumberFields.ideleClassNormMap F L).range.index ≤ p)

/-- **The second fundamental inequality for the global idele-class formation.** For every finite
normal layer `V ◁ U` of `G_K`, the order of `H²(U/V, C_L)` divides `[U : V]`. -/
theorem natCard_H2_globalFormation_dvd_degree
    (Lay : NormalLayer (AbsoluteGaloisGroup K)) :
    Nat.card (Lay.H (globalFormation K) 2) ∣ Lay.degree :=
  natCard_H2_globalFormation_dvd_degree_of_forall_index_le
    (fun F L _ _ _ _ _ _ p _ _ hfin ↦
      index_range_ideleClassNormMap_le_of_finrank_prime F L p hfin) Lay

end TauCeti.ClassFieldTheory
end

end
end
