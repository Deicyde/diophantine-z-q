-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Picard.Sheaf), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Presheaf
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# The relative Picard sheaf

The relative Picard functor is the fppf sheafification of the presheaf of
invertible module-sheaf classes on the fibers of a family. The natural map
from the presheaf is the unit of sheafification.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The relative Picard functor as an fppf sheaf. -/
def picardFunctor (f : X ⟶ S) : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (presheafToSheaf (Scheme.fppfTopology.over S) (Type (u + 1))).obj (picardPresheaf f)

/-- The canonical map from invertible module-sheaf classes to the Picard sheaf. -/
abbrev toPicardFunctor (f : X ⟶ S) : picardPresheaf f ⟶ (picardFunctor f).obj :=
  toSheafify (Scheme.fppfTopology.over S) (picardPresheaf f)

end AlgebraicGeometry
