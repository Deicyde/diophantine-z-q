-- Vendored from frenzymath/Jacobian-Challenge (https://github.com/frenzymath/Jacobian-Challenge, commit c4254cce15b3e284a0a3ae1d73936f2ee195d272, module Jacobian.CategoryTheory.Comma.Over.Pullback), Apache-2.0.
-- Copyright 2026 Axel Delaval, Jie Xu, and Shitan Xu; see LICENSE and NOTICE in ZInQKernel/Contrib/CloudW07JacobiansCurves/.
-- Changed for this repository: import paths moved under `ZInQKernel.Contrib.CloudW07JacobiansCurves`; names and namespaces unchanged.
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Projections of the canonical pullback comparisons

The identity and composite comparisons for pullback of objects over a base
preserve the projection to the original object. These formulas follow from the
counit equations for the adjunction mates defining the comparisons.
-/

universe u v

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

/-- The identity pullback comparison is the first pullback projection. -/
theorem pullbackId_hom_app_left (base : C) (object : Over base) :
    ((Over.pullbackId (X := base)).hom.app object).left =
      pullback.fst object.hom (𝟙 base) := by
  simp [Over.pullbackId, conjugateIsoEquiv, Over.mapId, Adjunction.id,
    Over.comp_left, Over.mapPullbackAdj_counit_app]

/-- The composite pullback comparison preserves the projection to the original object. -/
theorem pullbackComp_hom_app_left_fst_fst {base middle extension : C}
    (firstMap : extension ⟶ middle) (secondMap : middle ⟶ base) (object : Over base) :
    ((Over.pullbackComp firstMap secondMap).hom.app object).left ≫
      pullback.fst (pullback.snd object.hom secondMap) firstMap ≫
        pullback.fst object.hom secondMap =
      pullback.fst object.hom (firstMap ≫ secondMap) := by
  have comparison := conjugateEquiv_counit (Over.mapPullbackAdj (firstMap ≫ secondMap))
    ((Over.mapPullbackAdj firstMap).comp (Over.mapPullbackAdj secondMap))
    (Over.mapComp firstMap secondMap).inv object
  rw [Adjunction.comp_counit_app] at comparison
  have projection := congrArg (fun morphism ↦ morphism.left) comparison
  simpa [Over.pullbackComp, conjugateIsoEquiv, Over.mapComp, Over.comp_left,
    Over.mapPullbackAdj_counit_app, Category.assoc] using projection

end CategoryTheory.Over
