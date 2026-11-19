/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Native chosen-line triple equality on the ACTUAL triple diagonal, split into
opaque chart maps and separately checked actual restriction proofs. This is
DIAGONAL only, not global ActualLineCocycle or ampleness.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorTests
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineCoefficientTriple
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineAbstractFamilyComposition
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTripleChartGeometry

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

abbrev tensorDMap1 := (TensorTripleChartGeometry.D R' V G A e c hV).ι ≫
  (chart13 (R := R) R' G ≫ projection1 (R := R) R' G)
abbrev tensorDMap2 := (TensorTripleChartGeometry.D R' V G A e c hV).ι ≫
  (chart23 R' V G A e c hV ≫ projection1 (R := R) R' G)
abbrev tensorDMap3 := (TensorTripleChartGeometry.D R' V G A e c hV).ι ≫
  (chart13 (R := R) R' G ≫ projection2 R' V G A e c hV)

/-- Actual chosen 12-chart line map, with literal endpoint morphisms. -/
def tensorDLine12 :
    (modulesPseudofunctor.map (tensorDMap1 R' V G A e c hV).op.toLoc).toFunctor.obj M ⟶
      (modulesPseudofunctor.map (tensorDMap2 R' V G A e c hV).op.toLoc).toFunctor.obj M :=
  pullHom (F := modulesPseudofunctor)
    (f₁ := projection1 (R := R) R' G) (f₂ := projection2 R' V G A e c hV)
    (M₁ := M) (M₂ := M) (tensorLineIso R' V G A e c hV M L β).hom
    ((TensorTripleChartGeometry.D R' V G A e c hV).ι ≫ chart12 (R := R) R' G)
    (tensorDMap1 R' V G A e c hV) (tensorDMap2 R' V G A e c hV)
    (by simpa only [Category.assoc] using
      congrArg ((TensorTripleChartGeometry.D R' V G A e c hV).ι ≫ ·) (nerve_eq1 (R := R) R' G))
    (by simpa only [Category.assoc] using
      congrArg ((TensorTripleChartGeometry.D R' V G A e c hV).ι ≫ ·) (nerve_eq2 R' V G A e c hV))

/-- Actual chosen 23-chart line map, with literal endpoint morphisms. -/
def tensorDLine23 :
    (modulesPseudofunctor.map (tensorDMap2 R' V G A e c hV).op.toLoc).toFunctor.obj M ⟶
      (modulesPseudofunctor.map (tensorDMap3 R' V G A e c hV).op.toLoc).toFunctor.obj M :=
  pullHom (F := modulesPseudofunctor)
    (f₁ := projection1 (R := R) R' G) (f₂ := projection2 R' V G A e c hV)
    (M₁ := M) (M₂ := M) (tensorLineIso R' V G A e c hV M L β).hom
    ((TensorTripleChartGeometry.D R' V G A e c hV).ι ≫ chart23 R' V G A e c hV)
    (tensorDMap2 R' V G A e c hV) (tensorDMap3 R' V G A e c hV)
    (by simp only [tensorDMap2, Category.assoc])
    (by simpa only [Category.assoc] using
      congrArg ((TensorTripleChartGeometry.D R' V G A e c hV).ι ≫ ·) (nerve_eq3 R' V G A e c hV).symm)

/-- Actual chosen 13-chart line map, with literal endpoint morphisms. -/
def tensorDLine13 :
    (modulesPseudofunctor.map (tensorDMap1 R' V G A e c hV).op.toLoc).toFunctor.obj M ⟶
      (modulesPseudofunctor.map (tensorDMap3 R' V G A e c hV).op.toLoc).toFunctor.obj M :=
  pullHom (F := modulesPseudofunctor)
    (f₁ := projection1 (R := R) R' G) (f₂ := projection2 R' V G A e c hV)
    (M₁ := M) (M₂ := M) (tensorLineIso R' V G A e c hV M L β).hom
    ((TensorTripleChartGeometry.D R' V G A e c hV).ι ≫ chart13 (R := R) R' G)
    (tensorDMap1 R' V G A e c hV) (tensorDMap3 R' V G A e c hV)
    (by simp only [tensorDMap1, Category.assoc]) (by simp only [tensorDMap3, Category.assoc])

/-- The prescribed 12 map is the ACTUAL canonical equality comparison on D. -/
theorem tensorDLine12_spec :
    ∃ h : tensorDMap1 R' V G A e c hV = tensorDMap2 R' V G A e c hV,
      tensorDLine12 R' V G A e c hV M L β = (coefficientEqIso M h).hom :=
  tensorLineIso_on_diagonal R' V G A e c hV M L β
    ((TensorTripleChartGeometry.D R' V G A e c hV).ι ≫ chart12 (R := R) R' G)
    (by simpa only [Category.assoc] using TensorTripleChartGeometry.diagonal_chart12 R' V G A e c hV)
    (tensorDMap1 R' V G A e c hV) (tensorDMap2 R' V G A e c hV)
    (by simpa only [tensorDMap1, Category.assoc] using
      congrArg ((TensorTripleChartGeometry.D R' V G A e c hV).ι ≫ ·) (nerve_eq1 (R := R) R' G))
    (by simpa only [tensorDMap2, Category.assoc] using
      congrArg ((TensorTripleChartGeometry.D R' V G A e c hV).ι ≫ ·) (nerve_eq2 R' V G A e c hV))

theorem tensorDLine23_spec :
    ∃ h : tensorDMap2 R' V G A e c hV = tensorDMap3 R' V G A e c hV,
      tensorDLine23 R' V G A e c hV M L β = (coefficientEqIso M h).hom :=
  tensorLineIso_on_diagonal R' V G A e c hV M L β
    ((TensorTripleChartGeometry.D R' V G A e c hV).ι ≫ chart23 R' V G A e c hV)
    (by simpa only [Category.assoc] using TensorTripleChartGeometry.diagonal_chart23 R' V G A e c hV)
    (tensorDMap2 R' V G A e c hV) (tensorDMap3 R' V G A e c hV)
    (by simp only [tensorDMap2, Category.assoc])
    (by simpa only [tensorDMap3, Category.assoc] using
      congrArg ((TensorTripleChartGeometry.D R' V G A e c hV).ι ≫ ·) (nerve_eq3 R' V G A e c hV).symm)

theorem tensorDLine13_spec :
    ∃ h : tensorDMap1 R' V G A e c hV = tensorDMap3 R' V G A e c hV,
      tensorDLine13 R' V G A e c hV M L β = (coefficientEqIso M h).hom :=
  tensorLineIso_on_diagonal R' V G A e c hV M L β
    ((TensorTripleChartGeometry.D R' V G A e c hV).ι ≫ chart13 (R := R) R' G)
    (by simpa only [Category.assoc] using TensorTripleChartGeometry.diagonal_chart13 R' V G A e c hV)
    (tensorDMap1 R' V G A e c hV) (tensorDMap3 R' V G A e c hV)
    (by simp only [tensorDMap1, Category.assoc]) (by simp only [tensorDMap3, Category.assoc])

/-- The actual native 12/23 chart maps compose to 13 on the actual diagonal. -/
theorem tensorLineIso_triple_diagonal :
    tensorDLine12 R' V G A e c hV M L β ≫ tensorDLine23 R' V G A e c hV M L β =
      tensorDLine13 R' V G A e c hV M L β := by
  obtain ⟨h12, e12⟩ := tensorDLine12_spec R' V G A e c hV M L β
  obtain ⟨h23, e23⟩ := tensorDLine23_spec R' V G A e c hV M L β
  obtain ⟨h13, e13⟩ := tensorDLine13_spec R' V G A e c hV M L β
  exact Abstract.familyEquality_composition
    (D := modulesPseudofunctor.obj
      (.mk (op (TensorTripleChartGeometry.D R' V G A e c hV).toScheme)))
    (fun f : (TensorTripleChartGeometry.D R' V G A e c hV).toScheme ⟶ G.X.left =>
      (modulesPseudofunctor.map f.op.toLoc).toFunctor.obj M)
    (tensorDMap1 R' V G A e c hV) (tensorDMap2 R' V G A e c hV)
    (tensorDMap3 R' V G A e c hV) h12 h23 h13
    (tensorDLine12 R' V G A e c hV M L β)
    (tensorDLine23 R' V G A e c hV M L β)
    (tensorDLine13 R' V G A e c hV M L β)
    e12 e23 e13

#print axioms tensorLineIso_triple_diagonal

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
