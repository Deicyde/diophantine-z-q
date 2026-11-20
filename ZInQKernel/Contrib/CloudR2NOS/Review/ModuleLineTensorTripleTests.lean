/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Global triple native homs and their literal D/H tests. Every native map is
pulled from the actual chosen tensor-square psi. No global cocycle equality
or ampleness/extension conclusion is an input.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorDiagonalTriple
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorGenericTriple
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineAbstractTestPull

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
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

abbrev tensorTripleMap1 := chart13 (R := R) R' G ≫ projection1 (R := R) R' G
abbrev tensorTripleMap2 := chart23 R' V G A e c hV ≫ projection1 (R := R) R' G
abbrev tensorTripleMap3 := chart13 (R := R) R' G ≫ projection2 R' V G A e c hV

def tensorTripleLine12 :
    (modulesPseudofunctor.map (tensorTripleMap1 (R := R) R' G).op.toLoc).toFunctor.obj M ⟶
      (modulesPseudofunctor.map (tensorTripleMap2 R' V G A e c hV).op.toLoc).toFunctor.obj M :=
  pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
    (f₁ := projection1 (R := R) R' G) (f₂ := projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β).hom (chart12 (R := R) R' G)
    (tensorTripleMap1 (R := R) R' G) (tensorTripleMap2 R' V G A e c hV)
    (nerve_eq1 (R := R) R' G) (nerve_eq2 R' V G A e c hV)

def tensorTripleLine23 :
    (modulesPseudofunctor.map (tensorTripleMap2 R' V G A e c hV).op.toLoc).toFunctor.obj M ⟶
      (modulesPseudofunctor.map (tensorTripleMap3 R' V G A e c hV).op.toLoc).toFunctor.obj M :=
  pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
    (f₁ := projection1 (R := R) R' G) (f₂ := projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β).hom (chart23 R' V G A e c hV)
    (tensorTripleMap2 R' V G A e c hV) (tensorTripleMap3 R' V G A e c hV)
    rfl (nerve_eq3 R' V G A e c hV).symm

def tensorTripleLine13 :
    (modulesPseudofunctor.map (tensorTripleMap1 (R := R) R' G).op.toLoc).toFunctor.obj M ⟶
      (modulesPseudofunctor.map (tensorTripleMap3 R' V G A e c hV).op.toLoc).toFunctor.obj M :=
  pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
    (f₁ := projection1 (R := R) R' G) (f₂ := projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β).hom (chart13 (R := R) R' G)
    (tensorTripleMap1 (R := R) R' G) (tensorTripleMap3 R' V G A e c hV) rfl rfl

/-- Literal direct test of the global 12 hom on actual D. -/
theorem tensorTripleLine12_on_D :
    pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
      (f₁ := tensorTripleMap1 (R := R) R' G) (f₂ := tensorTripleMap2 R' V G A e c hV)
      (tensorTripleLine12 R' V G A e c hV M L β) (TensorTripleChartGeometry.D R' V G A e c hV).ι
      (tensorDMap1 R' V G A e c hV) (tensorDMap2 R' V G A e c hV) rfl rfl =
      tensorDLine12 R' V G A e c hV M L β :=
  Abstract.test_pullHom (F := modulesPseudofunctor)
    (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β).hom (chart12 (R := R) R' G)
    (tensorTripleMap1 (R := R) R' G) (tensorTripleMap2 R' V G A e c hV)
    (nerve_eq1 (R := R) R' G) (nerve_eq2 R' V G A e c hV)
    (TensorTripleChartGeometry.D R' V G A e c hV).ι _ _ rfl rfl

theorem tensorTripleLine23_on_D :
    pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
      (f₁ := tensorTripleMap2 R' V G A e c hV) (f₂ := tensorTripleMap3 R' V G A e c hV)
      (tensorTripleLine23 R' V G A e c hV M L β) (TensorTripleChartGeometry.D R' V G A e c hV).ι
      (tensorDMap2 R' V G A e c hV) (tensorDMap3 R' V G A e c hV) rfl rfl =
      tensorDLine23 R' V G A e c hV M L β :=
  Abstract.test_pullHom (F := modulesPseudofunctor)
    (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β).hom (chart23 R' V G A e c hV)
    (tensorTripleMap2 R' V G A e c hV) (tensorTripleMap3 R' V G A e c hV)
    rfl (nerve_eq3 R' V G A e c hV).symm (TensorTripleChartGeometry.D R' V G A e c hV).ι _ _ rfl rfl

theorem tensorTripleLine13_on_D :
    pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
      (f₁ := tensorTripleMap1 (R := R) R' G) (f₂ := tensorTripleMap3 R' V G A e c hV)
      (tensorTripleLine13 R' V G A e c hV M L β) (TensorTripleChartGeometry.D R' V G A e c hV).ι
      (tensorDMap1 R' V G A e c hV) (tensorDMap3 R' V G A e c hV) rfl rfl =
      tensorDLine13 R' V G A e c hV M L β :=
  Abstract.test_pullHom (F := modulesPseudofunctor)
    (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β).hom (chart13 (R := R) R' G)
    (tensorTripleMap1 (R := R) R' G) (tensorTripleMap3 R' V G A e c hV)
    rfl rfl (TensorTripleChartGeometry.D R' V G A e c hV).ι _ _ rfl rfl

/-- Literal direct test of the global 12 hom on actual H. -/
theorem tensorTripleLine12_on_H :
    pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
      (f₁ := tensorTripleMap1 (R := R) R' G) (f₂ := tensorTripleMap2 R' V G A e c hV)
      (tensorTripleLine12 R' V G A e c hV M L β) (TensorTripleChartGeometry.H (R := R) R' V G).ι
      (tensorHMap1 (R := R) R' V G) (tensorHMap2 R' V G A e c hV) rfl rfl =
      tensorHLine12 R' V G A e c hV M L β :=
  Abstract.test_pullHom (F := modulesPseudofunctor)
    (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β).hom (chart12 (R := R) R' G)
    (tensorTripleMap1 (R := R) R' G) (tensorTripleMap2 R' V G A e c hV)
    (nerve_eq1 (R := R) R' G) (nerve_eq2 R' V G A e c hV)
    (TensorTripleChartGeometry.H (R := R) R' V G).ι _ _ rfl rfl

theorem tensorTripleLine23_on_H :
    pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
      (f₁ := tensorTripleMap2 R' V G A e c hV) (f₂ := tensorTripleMap3 R' V G A e c hV)
      (tensorTripleLine23 R' V G A e c hV M L β) (TensorTripleChartGeometry.H (R := R) R' V G).ι
      (tensorHMap2 R' V G A e c hV) (tensorHMap3 R' V G A e c hV) rfl rfl =
      tensorHLine23 R' V G A e c hV M L β :=
  Abstract.test_pullHom (F := modulesPseudofunctor)
    (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β).hom (chart23 R' V G A e c hV)
    (tensorTripleMap2 R' V G A e c hV) (tensorTripleMap3 R' V G A e c hV)
    rfl (nerve_eq3 R' V G A e c hV).symm (TensorTripleChartGeometry.H (R := R) R' V G).ι _ _ rfl rfl

theorem tensorTripleLine13_on_H :
    pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
      (f₁ := tensorTripleMap1 (R := R) R' G) (f₂ := tensorTripleMap3 R' V G A e c hV)
      (tensorTripleLine13 R' V G A e c hV M L β) (TensorTripleChartGeometry.H (R := R) R' V G).ι
      (tensorHMap1 (R := R) R' V G) (tensorHMap3 R' V G A e c hV) rfl rfl =
      tensorHLine13 R' V G A e c hV M L β :=
  Abstract.test_pullHom (F := modulesPseudofunctor)
    (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β).hom (chart13 (R := R) R' G)
    (tensorTripleMap1 (R := R) R' G) (tensorTripleMap3 R' V G A e c hV)
    rfl rfl (TensorTripleChartGeometry.H (R := R) R' V G).ι _ _ rfl rfl

#print axioms tensorTripleLine12_on_D
#print axioms tensorTripleLine23_on_D
#print axioms tensorTripleLine13_on_D
#print axioms tensorTripleLine12_on_H
#print axioms tensorTripleLine23_on_H
#print axioms tensorTripleLine13_on_H

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
