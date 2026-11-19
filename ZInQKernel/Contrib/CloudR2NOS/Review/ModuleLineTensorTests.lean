/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Actual chosen-psi restrictions on arbitrary diagonal/generic test morphisms.
Only actual geometric factor maps and the proved chart equations are used.
No tensor-triple cocycle, line-extension, ampleness or NOS Fact is introduced.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTestLifts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat
open ZInQ.Contrib.CloudR2NOS.GoodDescent
open ZInQ.Contrib.CloudR2NOS.GoodDescent.GenericModel
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

/-- Morphism-valued equality of original chart bases gives an actual diagonal factor. -/
theorem tensorLineDiagonal_factor {T : Scheme.{u}}
    (t : T ⟶ model2 (R := R) R' G)
    (ht : t ≫ (projection1 (R := R) R' G ≫ G.X.hom) =
      t ≫ (structure2 (R := R) R' G ≫ right R R')) :
    ∃ d : T ⟶ (tensorLineDiagonal (R := R) R' G).toScheme,
      d ≫ (tensorLineDiagonal (R := R) R' G).ι = t := by
  apply exists_equalityOpen_lift (baseMap R R')
    (projection1 (R := R) R' G ≫ G.X.hom)
    (structure2 (R := R) R' G ≫ right R R') _ t ht

/-- The chosen native map on a diagonal test is the canonical equality map,
with BOTH source and target kept as their actual original composites. -/
theorem tensorLineIso_on_diagonal {T : Scheme.{u}}
    (t : T ⟶ model2 (R := R) R' G)
    (ht : t ≫ (projection1 (R := R) R' G ≫ G.X.hom) =
      t ≫ (structure2 (R := R) R' G ≫ right R R'))
    (x y : T ⟶ G.X.left)
    (hx : t ≫ projection1 (R := R) R' G = x)
    (hy : t ≫ projection2 R' V G A e c hV = y) :
    ∃ hxy : x = y,
      pullHom (F := modulesPseudofunctor) (tensorLineIso R' V G A e c hV M L β).hom
        t x y hx hy = (coefficientEqIso M hxy).hom := by
  obtain ⟨d, hd⟩ := tensorLineDiagonal_factor R' G t ht
  let D := tensorLineDiagonal (R := R) R' G
  have hdx : d ≫ (D.ι ≫ projection1 (R := R) R' G) = x := by
    rw [← Category.assoc, hd, hx]
  have hdy : d ≫ (D.ι ≫ projection2 R' V G A e c hV) = y := by
    rw [← Category.assoc, hd, hy]
  let hxy := hdx.symm.trans ((congrArg (d ≫ ·) (tensor_line_diagonal_eq R' V G A e c hV)).trans hdy)
  refine ⟨hxy, ?_⟩
  have hm := Abstract.pullHom_of_chart_map_comp (F := modulesPseudofunctor)
    (projection1 (R := R) R' G) (projection2 R' V G A e c hV) D.ι
    (tensorLineIso R' V G A e c hV M L β).hom
    (coefficientEqIso M (tensor_line_diagonal_eq R' V G A e c hV)).hom
    (by rw [← iteratedLineIso_hom]; exact tensorLineIso_diagonal R' V G A e c hV M L β)
    d t hd x y hx hy
  exact hm.trans (coefficientEqIso_pullHom M (tensor_line_diagonal_eq R' V G A e c hV)
    d x y hdx hdy)

/-- An arbitrary generic test factors through the literal source generic open. -/
theorem tensorLineGeneric_factor {T : Scheme.{u}}
    (t : T ⟶ model2 (R := R) R' G)
    (ht : ∀ a : T, t a ∈ modelSquareGenericOpen R' V G) :
    ∃ h : T ⟶ (modelSquareGenericOpen R' V G).toScheme,
      h ≫ (modelSquareGenericOpen R' V G).ι = t :=
  ⟨intoOpen t (modelSquareGenericOpen R' V G) ht,
    intoOpen_ι t (modelSquareGenericOpen R' V G) ht⟩

#print axioms tensorLineDiagonal_factor
#print axioms tensorLineIso_on_diagonal
#print axioms tensorLineGeneric_factor

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
