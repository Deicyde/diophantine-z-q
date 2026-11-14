-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.CategoryTheory.Abelian.Injective.Cycles), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.CategoryTheory.Abelian.Injective.Resolution

/-!
# Zeroth cycles of an injective resolution

The kernel property identifies the resolved object with the zeroth cycles,
naturally with respect to comparison maps of resolutions.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

namespace CategoryTheory.InjectiveResolution
variable {C : Type*} [Category* C] [Abelian C]

/-- The object resolved by an injective resolution is its zeroth cycles. -/
def isoCyclesZero {Z : C} (I : InjectiveResolution Z) : Z ≅ I.cocomplex.cycles 0 :=
  IsLimit.conePointUniqueUpToIso I.isLimitKernelFork (I.cocomplex.cyclesIsKernel 0 1 (by simp))

@[reassoc]
lemma isoCyclesZero_hom_iCycles {Z : C} (I : InjectiveResolution Z) :
    I.isoCyclesZero.hom ≫ I.cocomplex.iCycles 0 = I.ι.f 0 :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

/-- The identification of the resolved object with the zeroth cycles is natural with respect to
the lift `InjectiveResolution.desc` of a morphism. -/
lemma isoCyclesZero_inv_naturality {Y Z : C} (g : Z ⟶ Y) (I : InjectiveResolution Y)
    (J : InjectiveResolution Z) :
    J.isoCyclesZero.inv ≫ g =
      HomologicalComplex.cyclesMap (InjectiveResolution.desc g I J) 0 ≫ I.isoCyclesZero.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, ← cancel_mono (I.cocomplex.iCycles 0)]
  simp [isoCyclesZero_hom_iCycles_assoc, isoCyclesZero_hom_iCycles]


end CategoryTheory.InjectiveResolution
