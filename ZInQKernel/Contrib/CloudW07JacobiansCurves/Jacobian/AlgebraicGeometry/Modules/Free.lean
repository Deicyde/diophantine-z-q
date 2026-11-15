-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.AlgebraicGeometry.Modules.Free), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Invertible
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.Topology.Category.TopCat.OpensPullback

/-!
# Pullback of free module sheaves

Pullback preserves free module sheaves on a fixed set of generators.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
open SheafOfModules
variable {X Y : Scheme.{u}}
/-- Pullback carries a free sheaf on a set to the free sheaf on the same set. -/
noncomputable def pullbackFreeIso (g : Y ⟶ X) (I : Type u) :
    (pullback g).obj (free (R := X.ringCatSheaf) I) ≅ free I :=
  SheafOfModules.pullbackObjFreeIso g.toRingCatSheafHom I

end AlgebraicGeometry.Scheme.Modules
