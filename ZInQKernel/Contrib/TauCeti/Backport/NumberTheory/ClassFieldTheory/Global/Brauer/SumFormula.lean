/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Brauer.SumFormula

public section
noncomputable section

namespace TauCeti.ClassFieldTheory

open _root_.IntermediateField
variable (K : Type) [Field K] [NumberField K]

/-- **The Hasse principle for the Brauer group** (Albert–Brauer–Hasse–Noether). A Brauer class of
the number field `K` whose localizations at all places vanish is zero: `Br K → ⨁_v Br K_v` is
injective. -/
theorem brLocalization_injective : Function.Injective (brLocalization K) :=
  brLocalization_injective_of_subsingleton_h1_globalFormation K fun _ ↦
    subsingleton_h1_globalFormation _

end TauCeti.ClassFieldTheory

namespace TauCeti.ClassFieldTheory

open _root_.IntermediateField
variable (K : Type) [Field K] [NumberField K]

/-- **The sum formula.** The local invariants of every Brauer class of the number field `K` sum
to zero. -/
@[simp]
theorem sumLocalInv_brLocalization_eq_zero (x : Br K) : sumLocalInv K (brLocalization K x) = 0 :=
  sumLocalInv_brLocalization_eq_zero_of_brLocalization_injective K
    (fun E _ _ _ ↦ brLocalization_injective E) x

end TauCeti.ClassFieldTheory

end
end
