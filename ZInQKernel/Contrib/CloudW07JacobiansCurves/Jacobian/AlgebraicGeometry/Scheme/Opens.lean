-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Scheme.Opens), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.AlgebraicGeometry.Scheme

/-!
# Inverse images of scheme opens
-/

universe u

namespace AlgebraicGeometry.Scheme.Hom

lemma preimage_iInf {sourceScheme targetScheme : Scheme.{u}}
    (morphism : sourceScheme ⟶ targetScheme) {indexType : Type*} [Finite indexType]
    (opensFamily : indexType → targetScheme.Opens) :
    morphism ⁻¹ᵁ ⨅ index, opensFamily index = ⨅ index, morphism ⁻¹ᵁ opensFamily index := by
  apply TopologicalSpace.Opens.ext
  simp only [Scheme.Hom.coe_preimage, TopologicalSpace.Opens.coe_iInf, Set.preimage_iInter]

end AlgebraicGeometry.Scheme.Hom
