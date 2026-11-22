-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.Algebra.Category.ModuleCat.Sheaf.Evaluation), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Evaluation of sheaves of modules

Taking sections over an object is additive in the coefficient sheaf.
-/

universe v v' u u'

open CategoryTheory

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) (U : Cᵒᵖ)

instance evaluation_additive : (evaluation.{v} R U).Additive where
  map_add := rfl

end SheafOfModules
