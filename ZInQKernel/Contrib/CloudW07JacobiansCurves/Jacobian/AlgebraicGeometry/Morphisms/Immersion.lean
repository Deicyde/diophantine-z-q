-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Morphisms.Immersion), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Composition of immersions with open immersions

An immersion followed by an open immersion is an immersion. This gives the
right-composition property used when checking immersions on a cover of the target.
-/

namespace AlgebraicGeometry.IsImmersion

instance respectsRight_isOpenImmersion :
    CategoryTheory.MorphismProperty.RespectsRight @IsImmersion @IsOpenImmersion where
  postcomp openImmersion isOpenImmersion immersion isImmersion := by
    have : IsOpenImmersion openImmersion := isOpenImmersion
    have : IsImmersion immersion := isImmersion
    infer_instance

end AlgebraicGeometry.IsImmersion
