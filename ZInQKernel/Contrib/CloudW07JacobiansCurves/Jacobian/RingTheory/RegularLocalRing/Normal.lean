-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.RingTheory.RegularLocalRing.Normal), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.RingTheory.RegularLocalRing.Domain
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Normality of regular local rings in dimension at most one

A regular local ring of dimension at most one is a field or a discrete
valuation ring. In either case it is integrally closed.
-/

noncomputable section

/-- A regular local ring of Krull dimension at most one is integrally closed. -/
theorem IsRegularLocalRing.isIntegrallyClosed (ring : Type*) [CommRing ring]
    [IsRegularLocalRing ring] (dimensionBound : ringKrullDim ring ≤ 1) :
    IsIntegrallyClosed ring := by
  by_cases field : IsField ring
  · letI := field.toField
    infer_instance
  have dimension : ringKrullDim ring = 1 := by
    refine le_antisymm dimensionBound (not_lt.mp fun smaller ↦ field ?_)
    have : Ring.KrullDimLE 0 ring :=
      Ring.krullDimLE_iff.mpr (ENat.WithBot.lt_add_one_iff.mp (by simpa using smaller))
    exact Ring.KrullDimLE.isField_of_isDomain
  have := IsRegularLocalRing.isDiscreteValuationRing ring dimension
  infer_instance
