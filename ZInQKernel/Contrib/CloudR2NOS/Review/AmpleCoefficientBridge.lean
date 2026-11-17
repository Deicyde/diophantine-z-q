/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Actual predicate bridge between the canonical source's native local-triviality
IsInvertible and W07's sheaf invertibility. Their equality is proved from the
literal common pullback-unit criterion, not inferred from nominal similarity.
This bridges the actual M extension output to the Euler/H0 coefficient API.
-/
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Invertible

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension

/-- Both actual coefficient predicates are the SAME pointwise native triviality criterion. -/
theorem source_isInvertible_iff_sheaf {X : Scheme.{u}} (M : X.Modules) :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.IsInvertible M ↔
      M.IsInvertible := by
  constructor
  · intro h
    exact (Scheme.Modules.isInvertible_iff_forall_exists_pullback_unit M).mpr h.exists_trivialization
  · intro h
    exact ⟨(Scheme.Modules.isInvertible_iff_forall_exists_pullback_unit M).mp h⟩

#print axioms source_isInvertible_iff_sheaf

end ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension
