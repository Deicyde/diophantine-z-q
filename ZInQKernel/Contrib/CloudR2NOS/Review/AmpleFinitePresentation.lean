/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

ACTUAL finite presentation of a native invertible scheme module from the
same local trivializations. This is a coefficient proof, not an Euler,
ampleness, or NOS assumption.
-/
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Invertible
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Algebra.Category.ModuleCat.Sheaf.FinitePresentation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension

/-- Rank-one trivializations give actual finite local presentation data. -/
theorem isFinitePresentation_of_invertible {X : Scheme.{u}} (M : X.Modules) [M.IsInvertible] :
    M.IsFinitePresentation := by
  obtain ⟨I, U, hU, e⟩ :=
    (SheafOfModules.isInvertible_iff_exists_over_unit (M := M)).mp inferInstance
  haveI (i : I) : (M.over (U i)).IsFinitePresentation := by
    haveI : (SheafOfModules.unit (X.ringCatSheaf.over (U i))).IsFinitePresentation :=
      (SheafOfModules.presentationUnit (ringSheaf := X.ringCatSheaf.over (U i))).isFinitePresentation
    exact (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over (U i))).prop_of_iso
      (e i).some.symm inferInstance
  exact SheafOfModules.IsFinitePresentation.of_coversTop M U hU

#print axioms isFinitePresentation_of_invertible

end ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension
