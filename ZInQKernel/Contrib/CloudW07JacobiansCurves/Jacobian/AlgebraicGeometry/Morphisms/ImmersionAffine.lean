-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Morphisms.ImmersionAffine), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Morphisms.Immersion

/-!
# Affine preimages under immersions

An immersion is closed over its coborder range. The preimage of an affine open
contained in that range is therefore affine.
-/

universe schemeUniverse

namespace AlgebraicGeometry

lemma Scheme.Hom.isAffineOpen_preimage_of_le_coborderRange
    {source target : Scheme.{schemeUniverse}} (immersion : source ⟶ target)
    [IsImmersion immersion] {opens : target.Opens} (affine : IsAffineOpen opens)
    (inclusion : opens ≤ immersion.coborderRange) :
    IsAffineOpen (immersion ⁻¹ᵁ opens) := by
  have pulledBack := (affine.preimage_of_isOpenImmersion immersion.coborderRange.ι
    (by rwa [Scheme.Opens.opensRange_ι])).preimage immersion.liftCoborder
  rwa [← Scheme.Hom.comp_preimage, Scheme.Hom.liftCoborder_ι] at pulledBack

end AlgebraicGeometry
