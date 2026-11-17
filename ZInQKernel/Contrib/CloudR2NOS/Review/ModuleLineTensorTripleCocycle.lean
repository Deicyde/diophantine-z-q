/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

GLOBAL hom-cocycle of the actual chosen tensor-square line iso, proved by
actual native D/H restrictions and the whole-residue-fibre scheme cover.
No line cocycle, line effectiveness, extension or ampleness is assumed.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorTripleTests
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineAbstractTripleTestEquality

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

/-- Proved whole-residue-fibre cover of the literal original model triple. -/
theorem tensorTriple_diagonal_generic_cover :
    TensorTripleChartGeometry.D R' V G A e c hV ⊔ TensorTripleChartGeometry.H (R := R) R' V G = ⊤ :=
  triple_diagonal_sup_generic (baseMap R R') c V hV
    (TensorTripleChartGeometry.u1 (R := R) R' G) (TensorTripleChartGeometry.u2 R' V G A e c hV)
    (TensorTripleChartGeometry.u3 R' V G A e c hV)
    (TensorTripleChartGeometry.base12 R' V G A e c hV) (TensorTripleChartGeometry.base23 R' V G A e c hV)

/-- Coherent composite equality on the actual diagonal, using actual chart maps. -/
theorem tensorTriple_composite_on_D :
    pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
      (f₁ := tensorTripleMap1 (R := R) R' G) (f₂ := tensorTripleMap3 R' V G A e c hV)
      (tensorTripleLine12 R' V G A e c hV M L β ≫ tensorTripleLine23 R' V G A e c hV M L β)
      (TensorTripleChartGeometry.D R' V G A e c hV).ι
      (tensorDMap1 R' V G A e c hV) (tensorDMap3 R' V G A e c hV) rfl rfl =
    pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
      (f₁ := tensorTripleMap1 (R := R) R' G) (f₂ := tensorTripleMap3 R' V G A e c hV)
      (tensorTripleLine13 R' V G A e c hV M L β) (TensorTripleChartGeometry.D R' V G A e c hV).ι
      (tensorDMap1 R' V G A e c hV) (tensorDMap3 R' V G A e c hV) rfl rfl :=
  Abstract.triple_tests_equality (F := modulesPseudofunctor)
    (tensorTripleMap1 (R := R) R' G) (tensorTripleMap2 R' V G A e c hV) (tensorTripleMap3 R' V G A e c hV)
    (tensorTripleLine12 R' V G A e c hV M L β) (tensorTripleLine23 R' V G A e c hV M L β)
    (tensorTripleLine13 R' V G A e c hV M L β) (TensorTripleChartGeometry.D R' V G A e c hV).ι
    (tensorDMap1 R' V G A e c hV) (tensorDMap2 R' V G A e c hV) (tensorDMap3 R' V G A e c hV)
    rfl rfl rfl (tensorDLine12 R' V G A e c hV M L β) (tensorDLine23 R' V G A e c hV M L β)
    (tensorDLine13 R' V G A e c hV M L β) (tensorTripleLine12_on_D R' V G A e c hV M L β)
    (tensorTripleLine23_on_D R' V G A e c hV M L β) (tensorTripleLine13_on_D R' V G A e c hV M L β)
    (tensorLineIso_triple_diagonal R' V G A e c hV M L β)

/-- Coherent composite equality on the actual generic open, cancelling original beta. -/
theorem tensorTriple_composite_on_H :
    pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
      (f₁ := tensorTripleMap1 (R := R) R' G) (f₂ := tensorTripleMap3 R' V G A e c hV)
      (tensorTripleLine12 R' V G A e c hV M L β ≫ tensorTripleLine23 R' V G A e c hV M L β)
      (TensorTripleChartGeometry.H (R := R) R' V G).ι
      (tensorHMap1 (R := R) R' V G) (tensorHMap3 R' V G A e c hV) rfl rfl =
    pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
      (f₁ := tensorTripleMap1 (R := R) R' G) (f₂ := tensorTripleMap3 R' V G A e c hV)
      (tensorTripleLine13 R' V G A e c hV M L β) (TensorTripleChartGeometry.H (R := R) R' V G).ι
      (tensorHMap1 (R := R) R' V G) (tensorHMap3 R' V G A e c hV) rfl rfl :=
  Abstract.triple_tests_equality (F := modulesPseudofunctor)
    (tensorTripleMap1 (R := R) R' G) (tensorTripleMap2 R' V G A e c hV) (tensorTripleMap3 R' V G A e c hV)
    (tensorTripleLine12 R' V G A e c hV M L β) (tensorTripleLine23 R' V G A e c hV M L β)
    (tensorTripleLine13 R' V G A e c hV M L β) (TensorTripleChartGeometry.H (R := R) R' V G).ι
    (tensorHMap1 (R := R) R' V G) (tensorHMap2 R' V G A e c hV) (tensorHMap3 R' V G A e c hV)
    rfl rfl rfl (tensorHLine12 R' V G A e c hV M L β) (tensorHLine23 R' V G A e c hV M L β)
    (tensorHLine13 R' V G A e c hV M L β) (tensorTripleLine12_on_H R' V G A e c hV M L β)
    (tensorTripleLine23_on_H R' V G A e c hV M L β) (tensorTripleLine13_on_H R' V G A e c hV M L β)
    (tensorLineIso_triple_generic R' V G A e c hV M L β)

/-- GLOBAL composition law on the original triple; no hpsi/cocycle input. -/
theorem tensorLineIso_triple_hom_cocycle :
    tensorTripleLine12 R' V G A e c hV M L β ≫ tensorTripleLine23 R' V G A e c hV M L β =
      tensorTripleLine13 R' V G A e c hV M L β := by
  apply module_hom_ext_two (TensorTripleChartGeometry.D R' V G A e c hV)
    (TensorTripleChartGeometry.H (R := R) R' V G) (tensorTriple_diagonal_generic_cover R' V G A e c hV)
  · exact Abstract.map_eq_of_pullHom_eq (F := modulesPseudofunctor)
      (tensorTripleMap1 (R := R) R' G) (tensorTripleMap3 R' V G A e c hV)
      (tensorTripleLine12 R' V G A e c hV M L β ≫ tensorTripleLine23 R' V G A e c hV M L β)
      (tensorTripleLine13 R' V G A e c hV M L β) (TensorTripleChartGeometry.D R' V G A e c hV).ι
      (tensorDMap1 R' V G A e c hV) (tensorDMap3 R' V G A e c hV) rfl rfl
      (tensorTriple_composite_on_D R' V G A e c hV M L β)
  · exact Abstract.map_eq_of_pullHom_eq (F := modulesPseudofunctor)
      (tensorTripleMap1 (R := R) R' G) (tensorTripleMap3 R' V G A e c hV)
      (tensorTripleLine12 R' V G A e c hV M L β ≫ tensorTripleLine23 R' V G A e c hV M L β)
      (tensorTripleLine13 R' V G A e c hV M L β) (TensorTripleChartGeometry.H (R := R) R' V G).ι
      (tensorHMap1 (R := R) R' V G) (tensorHMap3 R' V G A e c hV) rfl rfl
      (tensorTriple_composite_on_H R' V G A e c hV M L β)

#print axioms tensorLineIso_triple_hom_cocycle

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
