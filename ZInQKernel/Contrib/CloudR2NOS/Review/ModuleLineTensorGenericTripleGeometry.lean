/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Actual shared original-variety coordinates of the three generic lifts. This
is scheme geometry only; no native module/line/cocycle conclusion is assumed.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTripleGenericGeometry

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.CloudR2NOS.GoodDescent
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorCofaces
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorNerve
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTripleChartGeometry
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTripleGenericGeometry

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
  (V : (Base R).Opens) (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
  (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
    (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
  [Etale (baseMap R R')] (c : Base R)
  [Mono ((baseMap R R').fiberToSpecResidueField c)]
  (hV : ∀ z : Base R, z ∉ V → z = c)

abbrev tensorHLift1 := factor13 (R := R) R' V G ≫ genericProjection1 R' V G
abbrev tensorHLift2 := factor23 R' V G A e c hV ≫ genericProjection1 R' V G
abbrev tensorHLift3 := factor13 (R := R) R' V G ≫ genericProjection2 R' V G A e c hV

/-- The first/middle generic lifts have the same actual original-q coordinate. -/
theorem tensorHLift12_originalCoordinate :
    tensorHLift1 R' V G ≫ (genericModelOfGroupIso (baseMap R R') V G A e).q =
      tensorHLift2 R' V G A e c hV ≫ (genericModelOfGroupIso (baseMap R R') V G A e).q := by
  have h := congrArg (factor12 (R := R) R' V G ≫ ·) (genericCoordinate_invariant R' V G A e c hV)
  simpa only [← Category.assoc, shared_generic_first R' V G,
    shared_generic_middle R' V G A e c hV] using h

/-- The first/last generic lifts have the same actual original-q coordinate. -/
theorem tensorHLift13_originalCoordinate :
    tensorHLift1 R' V G ≫ (genericModelOfGroupIso (baseMap R R') V G A e).q =
      tensorHLift3 R' V G A e c hV ≫ (genericModelOfGroupIso (baseMap R R') V G A e).q := by
  simpa only [Category.assoc] using congrArg (factor13 (R := R) R' V G ≫ ·)
    (genericCoordinate_invariant R' V G A e c hV)

#print axioms tensorHLift12_originalCoordinate
#print axioms tensorHLift13_originalCoordinate

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
