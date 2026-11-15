-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Descent.Finite), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.AffineLocal
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.Gluing
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Descent.InvariantAffineOpen

/-!
# Effective finite-flat descent of schemes

A scheme whose finite sets lie in affine open subschemes admits effective descent
along a surjective finite flat morphism locally of finite presentation. Invariant
affine neighbourhoods reduce the construction to affine descent, and the local
descents glue.
-/

universe schemeUniverse

open CategoryTheory Limits

namespace CategoryTheory.Over.DescentDatum

open AlgebraicGeometry

variable {source base : Scheme.{schemeUniverse}} {baseMap : source ⟶ base}

theorem isEffective_of_isFinite [IsFinite baseMap] [Flat baseMap]
    [LocallyOfFinitePresentation baseMap] [Surjective baseMap] {representation : Over source}
    (finite_affine : ∀ finiteSet : Set representation.left, finiteSet.Finite →
      ∃ openSubset : representation.left.Opens, IsAffineOpen openSubset ∧ finiteSet ⊆ openSubset)
    (datum : DescentDatum baseMap representation) : datum.IsEffective := by
  refine isEffective_of_forall_exists_mem fun point ↦ ?_
  obtain ⟨openSubset, point_mem, invariant, affineOpen, baseOpen, affineBase, overBase⟩ :=
    datum.exists_isInvariant_isAffineOpen finite_affine point
  exact ⟨openSubset, invariant, point_mem,
    datum.isEffective_restrict_of_isAffineOpen invariant affineOpen affineBase overBase⟩

end CategoryTheory.Over.DescentDatum
