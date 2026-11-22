-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.Algebra.Category.ModuleCat.Dual), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Dualization of modules as a functor

Taking the linear dual sends a linear map to its transpose and defines a
contravariant functor on modules over a commutative ring.
-/

noncomputable section

universe u v

open CategoryTheory

namespace ModuleCat

/-- The contravariant functor sending a module to its linear dual. -/
@[simps]
def dualFunctor (baseRing : Type u) [CommRing baseRing] :
    (ModuleCat.{v} baseRing)ᵒᵖ ⥤ ModuleCat.{max u v} baseRing where
  obj coefficient := ModuleCat.of baseRing (Module.Dual baseRing coefficient.unop)
  map morphism := ModuleCat.ofHom (Module.Dual.transpose morphism.unop.hom)

end ModuleCat
