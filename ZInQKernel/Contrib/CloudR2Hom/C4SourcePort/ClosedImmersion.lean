/-
Copyright (c) 2026 H70 source-port contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

This is an original thin application of Mathlib's closed-immersion and properness
APIs at commit 56a005855ea17e0b0958f73ec801ae140b0a1679.  The imported Mathlib
files retain their authorship and Apache-2.0 notices; no supplier file is edited.
-/
import Lean
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Proper immersions are closed immersions

This Mathlib-only helper upgrades the genuine finite-coordinate projective
immersion supplied by Jacobian-Challenge to a closed immersion.  The upgrade
uses universal closedness, not a chosen replacement scheme or a finiteness axiom.
-/

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Hom.C4SourcePort

universe u

/-- An actual universally closed preimmersion of schemes is a closed immersion. -/
theorem isClosedImmersion_of_universallyClosed
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsPreimmersion f] [UniversallyClosed f] :
    IsClosedImmersion f := by
  exact IsClosedImmersion.of_isPreimmersion f f.isClosedMap.isClosed_range

/-- In particular, an actual proper immersion is a closed immersion. -/
theorem isClosedImmersion_of_isProper
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f] [IsProper f] :
    IsClosedImmersion f :=
  isClosedImmersion_of_universallyClosed f

end ZInQ.Contrib.CloudR2Hom.C4SourcePort

/- Full declaration checks: theorem-kind and the entire telescope, not an example
   that can instantiate away an extra assumption.  Universe zero is H70's world. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let name := ``ZInQ.Contrib.CloudR2Hom.C4SourcePort.isClosedImmersion_of_universallyClosed
  let info ← Lean.getConstInfo name
  match info with
  | .thmInfo _ => pure ()
  | _ => Lean.throwError "C4 declaration is not a theorem: {name}"
  unless info.levelParams.length == 1 do
    Lean.throwError "unexpected C4 universe telescope: {info.levelParams}"
  let actual := info.type.instantiateLevelParams info.levelParams [Lean.Level.zero]
  let expected ← Lean.Elab.Term.elabType (← `(∀ {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsPreimmersion f] [UniversallyClosed f], IsClosedImmersion f))
  unless ← Lean.Meta.isDefEq actual expected do
    Lean.throwError "C4 full declaration type mismatch: {name}"
  let extraHypothesis ← Lean.Elab.Term.elabType (← `(True →
    ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) [IsPreimmersion f] [UniversallyClosed f],
      IsClosedImmersion f))
  if ← Lean.Meta.isDefEq actual extraHypothesis then
    Lean.throwError "C4 extra-hypothesis negative control failed"
  Lean.logInfo "C4 theorem-kind/full-type PASS; extra-hypothesis negative control PASS"

run_cmd Lean.Elab.Command.liftTermElabM do
  let name := ``ZInQ.Contrib.CloudR2Hom.C4SourcePort.isClosedImmersion_of_isProper
  let info ← Lean.getConstInfo name
  match info with
  | .thmInfo _ => pure ()
  | _ => Lean.throwError "C4 declaration is not a theorem: {name}"
  unless info.levelParams.length == 1 do
    Lean.throwError "unexpected C4 universe telescope: {info.levelParams}"
  let actual := info.type.instantiateLevelParams info.levelParams [Lean.Level.zero]
  let expected ← Lean.Elab.Term.elabType (← `(∀ {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsImmersion f] [IsProper f], IsClosedImmersion f))
  unless ← Lean.Meta.isDefEq actual expected do
    Lean.throwError "C4 full declaration type mismatch: {name}"
  Lean.logInfo "C4 proper-immersion theorem-kind/full-type PASS"

#print axioms ZInQ.Contrib.CloudR2Hom.C4SourcePort.isClosedImmersion_of_universallyClosed
#print axioms ZInQ.Contrib.CloudR2Hom.C4SourcePort.isClosedImmersion_of_isProper
