/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

The ACTUAL chosen native line iso on the original tensor square, with direct
restriction equations recovered from the literal chart equations. M/L/beta
remain explicit givens, not extension or ampleness hypotheses of a final NOS
provider. This file does not assert the tensor-triple line cocycle.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensor
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLinePullRestriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open ZInQ.Contrib.CloudR2NOS.GoodDescent
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorCofaces
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorNerve

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

variable {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
  (V : (Base R).Opens) (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
  (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
    (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
  [Etale (baseMap R R')] (c : Base R)
  [Mono ((baseMap R R').fiberToSpecResidueField c)]
  (hV : ∀ z : Base R, z ∉ V → z = c)
  (M : G.X.left.Modules) (L : A.X.left.Modules)
  (β : (Scheme.Modules.pullback (modelGenericOpen R' V G).ι).obj M ≅
    (Scheme.Modules.pullback (genericModelOfGroupIso (baseMap R R') V G A e).q).obj L)

/-- Choice of the actually proved global iso, not a new line-descent assumption. -/
def tensorLineIso :
    (Scheme.Modules.pullback (projection1 (R := R) R' G)).obj M ≅
      (Scheme.Modules.pullback (projection2 R' V G A e c hV)).obj M :=
  Classical.choose (exists_tensorLineIso_of_genericLine R' V G A e c hV M L β)

/-- The literal diagonal chart equation of this actual global iso. -/
theorem tensorLineIso_diagonal :
    (Scheme.Modules.pullback (tensorLineDiagonal (R := R) R' G).ι).map
        (tensorLineIso R' V G A e c hV M L β).hom =
      (iteratedLineIso M (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
        (tensorLineDiagonal (R := R) R' G).ι
        (coefficientEqIso M (tensor_line_diagonal_eq R' V G A e c hV))).hom :=
  (Classical.choose_spec (exists_tensorLineIso_of_genericLine R' V G A e c hV M L β)).1

/-- The literal original generic chart equation of this actual global iso. -/
theorem tensorLineIso_generic :
    let H := modelSquareGenericOpen R' V G
    let δH := genericLineCompare (modelGenericOpen R' V G).ι
      (genericModelOfGroupIso (baseMap R R') V G A e).q M L β
      (genericProjection1 R' V G) (genericProjection2 R' V G A e c hV)
      (H.ι ≫ projection1 (R := R) R' G) (H.ι ≫ projection2 R' V G A e c hV)
      (genericProjection1 R' V G ≫ (genericModelOfGroupIso (baseMap R R') V G A e).q)
      (genericProjection1_ι R' V G) (genericProjection2_ι R' V G A e c hV)
      rfl (genericCoordinate_invariant R' V G A e c hV).symm
    (Scheme.Modules.pullback H.ι).map (tensorLineIso R' V G A e c hV M L β).hom =
      (iteratedLineIso M (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
        H.ι δH).hom :=
  (Classical.choose_spec (exists_tensorLineIso_of_genericLine R' V G A e c hV M L β)).2

/-- Coherent direct pullback along the ACTUAL diagonal chart. -/
theorem tensorLineIso_pullHom_diagonal :
    pullHom (F := modulesPseudofunctor) (tensorLineIso R' V G A e c hV M L β).hom
      (tensorLineDiagonal (R := R) R' G).ι
      ((tensorLineDiagonal (R := R) R' G).ι ≫ projection1 (R := R) R' G)
      ((tensorLineDiagonal (R := R) R' G).ι ≫ projection2 R' V G A e c hV)
      rfl rfl = (coefficientEqIso M (tensor_line_diagonal_eq R' V G A e c hV)).hom := by
  apply Abstract.pullHom_of_chart_map (F := modulesPseudofunctor)
    (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (tensorLineDiagonal (R := R) R' G).ι
  rw [← iteratedLineIso_hom]
  exact tensorLineIso_diagonal R' V G A e c hV M L β

/-- Coherent direct pullback along the ACTUAL original generic chart. -/
theorem tensorLineIso_pullHom_generic :
    let H := modelSquareGenericOpen R' V G
    let δH := genericLineCompare (modelGenericOpen R' V G).ι
      (genericModelOfGroupIso (baseMap R R') V G A e).q M L β
      (genericProjection1 R' V G) (genericProjection2 R' V G A e c hV)
      (H.ι ≫ projection1 (R := R) R' G) (H.ι ≫ projection2 R' V G A e c hV)
      (genericProjection1 R' V G ≫ (genericModelOfGroupIso (baseMap R R') V G A e).q)
      (genericProjection1_ι R' V G) (genericProjection2_ι R' V G A e c hV)
      rfl (genericCoordinate_invariant R' V G A e c hV).symm
    pullHom (F := modulesPseudofunctor) (tensorLineIso R' V G A e c hV M L β).hom
      H.ι (H.ι ≫ projection1 (R := R) R' G)
      (H.ι ≫ projection2 R' V G A e c hV) rfl rfl = δH.hom := by
  apply Abstract.pullHom_of_chart_map (F := modulesPseudofunctor)
    (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (modelSquareGenericOpen R' V G).ι
  rw [← iteratedLineIso_hom]
  exact tensorLineIso_generic R' V G A e c hV M L β

#print axioms tensorLineIso
#print axioms tensorLineIso_diagonal
#print axioms tensorLineIso_generic
#print axioms tensorLineIso_pullHom_diagonal
#print axioms tensorLineIso_pullHom_generic

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
