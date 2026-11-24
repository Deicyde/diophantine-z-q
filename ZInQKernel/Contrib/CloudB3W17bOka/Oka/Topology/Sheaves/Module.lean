/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Equivalence
import Mathlib.Topology.Sheaves.Module

/-!
# Coherence and restriction to an open subspace

For a topological space `X`, a sheaf of rings `R` on `X` and an open `U`, Mathlib's
`TopologicalSpace.Opens.sheafOfModulesEquivOver` identifies sheaves of modules over `R.over U`
(on the site `Over U`) with sheaves of modules over `R|_U` (on the subspace `U`). It comes from the
equivalence of sites `TopologicalSpace.Opens.overEquivalence`, so by
`SheafOfModules.isCoherent_pushforward_of_equivalence` it preserves and reflects coherence.

## Main results

- `TopologicalSpace.Opens.isCoherent_sheafOfModulesEquivOver_functor_obj_iff`
-/

open CategoryTheory TopologicalSpace Limits

universe u

namespace TopologicalSpace.Opens

variable {X : TopCat.{u}} (U : Opens X) (R : X.Sheaf RingCat.{u})

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The second compatibility condition of `TopologicalSpace.Opens.sheafOfModulesEquivOver`, as a
standalone lemma (the first one holds by `rfl`). -/
lemma sheafOfModulesEquivOver_H₂ :
    (U.overPullbackSheafEquivOver.app R).inv.hom ≫
      U.overEquivalence.symm.functor.op.whiskerLeft
        (U.sheafRestrictSheafEquivOver.app R).inv.hom ≫
        Functor.whiskerRight (NatTrans.op U.overEquivalence.symm.unit)
          (U.sheafRestrict.obj R).obj = 𝟙 _ := by
  ext : 2
  simp [overPullbackSheafEquivOver, sheafRestrictSheafEquivOver, eqToHom_map, overEquivalence,
    IsOpenMap.functor]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **Coherence is invariant under `TopologicalSpace.Opens.sheafOfModulesEquivOver`**: a sheaf of
modules over `R.over U` is coherent if and only if the corresponding sheaf of modules over `R|_U`
on the subspace `U` is. -/
theorem isCoherent_sheafOfModulesEquivOver_functor_obj_iff (M : SheafOfModules.{u} (R.over U)) :
    ((U.sheafOfModulesEquivOver R).functor.obj M).IsCoherent ↔ M.IsCoherent :=
  ⟨fun h => SheafOfModules.isCoherent_of_isCoherent_pushforward_of_equivalence
      U.overEquivalence.symm _ _ rfl (sheafOfModulesEquivOver_H₂ U R)
      (U.sheafOfModulesEquivOverUnit R) M h,
    fun _ => SheafOfModules.isCoherent_pushforward_of_equivalence
      U.overEquivalence.symm _ _ rfl (sheafOfModulesEquivOver_H₂ U R)
      (U.sheafOfModulesEquivOverUnit R) M⟩

end TopologicalSpace.Opens
