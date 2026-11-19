/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Actual native line isomorphism on Lane5's frozen tensor-square scheme nerve.
All diagonal/generic inputs to the general adapter are DERIVED from its
original scheme/group transport and original generic coordinate. M and beta
remain explicit intermediate givens; this is not line extension or ampleness.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTransport
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GenericTensor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
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

private theorem tensor_transport_condition :
    (projection1 (R := R) R' G ≫ G.X.hom) ≫ baseMap R R' =
      (structure2 (R := R) R' G ≫ right R R') ≫ baseMap R R' := by
  rw [(cartesian1 (R := R) R' G).w, Category.assoc, left_base R R', ← Category.assoc]

/-- Literal second projection equals the already proved original transport. -/
theorem tensor_projection2_eq_transport :
    projection2 R' V G A e c hV =
      (genericModelOfGroupIso (baseMap R R') V G A e).transportMap c hV
        (projection1 (R := R) R' G) (structure2 (R := R) R' G ≫ right R R')
        (tensor_transport_condition (R := R) R' G) := by
  exact (genericModelOfGroupIso (baseMap R R') V G A e).comparisonMap_fst c hV
    (left R R') (right R R') (left_base R R')

/-- The concrete diagonal open of the original tensor-square transport. -/
abbrev tensorLineDiagonal : (model2 (R := R) R' G).Opens :=
  equalityOpen (baseMap R R') (projection1 (R := R) R' G ≫ G.X.hom)
    (structure2 (R := R) R' G ≫ right R R') (tensor_transport_condition (R := R) R' G)

/-- The actual original projection maps agree on the derived diagonal. -/
theorem tensor_line_diagonal_eq :
    (tensorLineDiagonal (R := R) R' G).ι ≫ projection1 (R := R) R' G =
      (tensorLineDiagonal (R := R) R' G).ι ≫ projection2 R' V G A e c hV := by
  rw [tensor_projection2_eq_transport R' V G A e c hV]
  exact ((genericModelOfGroupIso (baseMap R R') V G A e).transportMap_diagonal c hV
    (projection1 (R := R) R' G) (structure2 (R := R) R' G ≫ right R R')
    (tensor_transport_condition (R := R) R' G)).symm

include c hV in
/-- The concrete diagonal and original generic open cover the tensor square. -/
theorem tensor_line_cover :
    tensorLineDiagonal (R := R) R' G ⊔ modelSquareGenericOpen R' V G = ⊤ := by
  have he := equality_sup_generic_eq_top (baseMap R R') c V hV
    (projection1 (R := R) R' G ≫ G.X.hom) (structure2 (R := R) R' G ≫ right R R')
    (tensor_transport_condition (R := R) R' G)
  have hH : ((projection1 (R := R) R' G ≫ G.X.hom) ≫ baseMap R R') ⁻¹ᵁ V =
      modelSquareGenericOpen R' V G := by
    rw [(cartesian1 (R := R) R' G).w]
    simp only [modelSquareGenericOpen, Scheme.Hom.comp_preimage]
  rwa [hH] at he

/-- Construct an actual native line iso on the SAME effective tensor nerve.
The cover, diagonal equality and generic-coordinate equality are all proved,
not offered as new compatibility hypotheses. -/
theorem exists_tensorLineIso_of_genericLine
    (M : G.X.left.Modules) (L : A.X.left.Modules)
    (β : (Scheme.Modules.pullback (modelGenericOpen R' V G).ι).obj M ≅
      (Scheme.Modules.pullback (genericModelOfGroupIso (baseMap R R') V G A e).q).obj L) :
    let D := tensorLineDiagonal (R := R) R' G
    let H := modelSquareGenericOpen R' V G
    let δD := coefficientEqIso M (tensor_line_diagonal_eq R' V G A e c hV)
    let δH := genericLineCompare (modelGenericOpen R' V G).ι
      (genericModelOfGroupIso (baseMap R R') V G A e).q M L β
      (genericProjection1 R' V G) (genericProjection2 R' V G A e c hV)
      (H.ι ≫ projection1 (R := R) R' G) (H.ι ≫ projection2 R' V G A e c hV)
      (genericProjection1 R' V G ≫ (genericModelOfGroupIso (baseMap R R') V G A e).q)
      (genericProjection1_ι R' V G) (genericProjection2_ι R' V G A e c hV)
      rfl (genericCoordinate_invariant R' V G A e c hV).symm
    ∃ ψ : (Scheme.Modules.pullback (projection1 (R := R) R' G)).obj M ≅
        (Scheme.Modules.pullback (projection2 R' V G A e c hV)).obj M,
      (Scheme.Modules.pullback D.ι).map ψ.hom =
        (iteratedLineIso M (projection1 (R := R) R' G)
          (projection2 R' V G A e c hV) D.ι δD).hom ∧
      (Scheme.Modules.pullback H.ι).map ψ.hom =
        (iteratedLineIso M (projection1 (R := R) R' G)
          (projection2 R' V G A e c hV) H.ι δH).hom := by
  exact exists_lineIso_diagonal_generic (modelGenericOpen R' V G).ι
    (genericModelOfGroupIso (baseMap R R') V G A e).q M L β
    (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (tensorLineDiagonal (R := R) R' G) (modelSquareGenericOpen R' V G)
    (tensor_line_cover R' V G c hV) (tensor_line_diagonal_eq R' V G A e c hV)
    (genericProjection1 R' V G) (genericProjection2 R' V G A e c hV)
    (genericProjection1_ι R' V G) (genericProjection2_ι R' V G A e c hV)
    (genericCoordinate_invariant R' V G A e c hV)

#print axioms tensor_projection2_eq_transport
#print axioms tensor_line_diagonal_eq
#print axioms tensor_line_cover
#print axioms exists_tensorLineIso_of_genericLine

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
