/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
-- Backported from Tau Ceti (https://github.com/TauCetiProject/TauCeti, commit 97a5b23586f9, module
-- TauCeti.NumberTheory.ClassFieldTheory.Global.LiftingObstruction), Apache-2.0: declarations added to that module after commit 5a01f5fe, whose
-- version is vendored as `ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.LiftingObstruction`.
module

public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.LiftingObstruction
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Formation.CoefficientMap
public import ZInQKernel.Contrib.TauCeti.NumberTheory.ClassFieldTheory.Global.Formation
public import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.ContCohomology.LongExact
public import ZInQKernel.Contrib.TauCeti.RepresentationTheory.Homological.TateCohomology.Periodic

public noncomputable section

section
open CategoryTheory TauCeti.ContCohomology
namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K]
variable (L : NormalLayer (AbsoluteGaloisGroup K))

/-- `ideleToClassH2 K L` applies Mathlib's cohomology map of the quotient map onto the idele
classes of the layer. -/
theorem ideleToClassH2_apply (x : L.H (ideleFormation K) 2) :
    ideleToClassH2 K L x =
      groupCohomology.map (MonoidHom.id L.Gal) (L.repMap (ideleClassHom K)) 2 x := by
  -- The oct16 module does not expose the body of `ideleToClassH2`; unfold `ideleToClassH2_def`.
  rw [ideleToClassH2_def]
  rfl

end TauCeti.ClassFieldTheory
end

end
