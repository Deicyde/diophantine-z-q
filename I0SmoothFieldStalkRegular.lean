/-
Copyright (c) 2026 H5 contributors. Apache-2.0.
Lane5 native producer for C2's exact A2 SmoothFieldStalkRegular.{u}.
SOURCE ONLY / UNCOMPILED. Truth pre-check: smoothness over the regular
field spectrum makes EVERY original stalk regular local; no algebraic-
closedness, dimension, point-closedness or characteristic condition is added.

Reuse is of actual held native TauCeti/Mathlib source. Its smooth-regular
proof passes through standard-smooth/etale polynomial charts and ascends
regularity along their genuine flat local maps. This is not a Stacks
predicate/import bridge, a supplied regularity Fact, or A1's UFD assertion.
Original third-party Apache-2.0 notices remain in the unchanged imports.
-/
import Step2DelegatedInterfaces
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.Morphisms.Smooth.Regular

set_option autoImplicit false
noncomputable section
universe u

open AlgebraicGeometry CategoryTheory

namespace H5OriginalDVR.Lane5.I0Native

/-- EXACT C2 A2 consumer. Regularity is on X.presheaf.stalk x itself. -/
theorem smoothFieldStalkRegular :
    H5OriginalDVR.Lane2.Step2DelegatedInterfaces.SmoothFieldStalkRegular.{u} := by
  intro K _ X f _ x
  letI : IsRegularRing K := inferInstance
  letI : ∀ y : Spec (CommRingCat.of K),
      IsRegularLocalRing ((Spec (CommRingCat.of K)).presheaf.stalk y) :=
    fun y => TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_Spec
      (CommRingCat.of K) y
  exact TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth f x

end H5OriginalDVR.Lane5.I0Native
