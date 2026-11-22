/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Actual native generic triple comparison, preserving the original model and
original generic-line beta/q. The three shared lifts and their original
coordinates are proved geometry, not a desired line cocycle hypothesis.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorGenericCoordinates
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorGenericTripleGeometry
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineAbstractComposition

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
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTripleChartGeometry
open ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective.TensorTripleGenericGeometry

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

abbrev tensorHMap1 := (H (R := R) R' V G).ι ≫ (chart13 (R := R) R' G ≫ projection1 (R := R) R' G)
abbrev tensorHMap2 := (H (R := R) R' V G).ι ≫ (chart23 R' V G A e c hV ≫ projection1 (R := R) R' G)
abbrev tensorHMap3 := (H (R := R) R' V G).ι ≫ (chart13 (R := R) R' G ≫ projection2 R' V G A e c hV)
abbrev tensorHOriginalCoordinate := tensorHLift1 (R := R) R' V G ≫
  (genericModelOfGroupIso (baseMap R R') V G A e).q

theorem tensorHLift1_model : tensorHLift1 (R := R) R' V G ≫ (modelGenericOpen R' V G).ι =
    tensorHMap1 (R := R) R' V G := by
  simp only [tensorHLift1, tensorHMap1, Category.assoc, genericProjection1_ι, factor13_ι_assoc]

theorem tensorHLift2_model : tensorHLift2 R' V G A e c hV ≫ (modelGenericOpen R' V G).ι =
    tensorHMap2 R' V G A e c hV := by
  simp only [tensorHLift2, tensorHMap2, Category.assoc, genericProjection1_ι, factor23_ι_assoc]

theorem tensorHLift3_model : tensorHLift3 R' V G A e c hV ≫ (modelGenericOpen R' V G).ι =
    tensorHMap3 R' V G A e c hV := by
  simp only [tensorHLift3, tensorHMap3, Category.assoc, genericProjection2_ι, factor13_ι_assoc]

theorem tensorHLift2_original : tensorHLift2 R' V G A e c hV ≫
    (genericModelOfGroupIso (baseMap R R') V G A e).q = tensorHOriginalCoordinate R' V G A e :=
  (tensorHLift12_originalCoordinate R' V G A e c hV).symm

theorem tensorHLift3_original : tensorHLift3 R' V G A e c hV ≫
    (genericModelOfGroupIso (baseMap R R') V G A e).q = tensorHOriginalCoordinate R' V G A e :=
  (tensorHLift13_originalCoordinate R' V G A e c hV).symm

/-- Literal chosen-psi test map on H's original 12 chart. -/
def tensorHLine12 :
    (modulesPseudofunctor.map (tensorHMap1 (R := R) R' V G).op.toLoc).toFunctor.obj M ⟶
      (modulesPseudofunctor.map (tensorHMap2 R' V G A e c hV).op.toLoc).toFunctor.obj M :=
  pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
    (f₁ := projection1 (R := R) R' G) (f₂ := projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β).hom ((H (R := R) R' V G).ι ≫ chart12 (R := R) R' G)
    (tensorHMap1 (R := R) R' V G) (tensorHMap2 R' V G A e c hV)
    (by simpa only [tensorHMap1, Category.assoc] using congrArg ((H (R := R) R' V G).ι ≫ ·) (nerve_eq1 (R := R) R' G))
    (by simpa only [tensorHMap2, Category.assoc] using congrArg ((H (R := R) R' V G).ι ≫ ·) (nerve_eq2 R' V G A e c hV))

def tensorHLine23 :
    (modulesPseudofunctor.map (tensorHMap2 R' V G A e c hV).op.toLoc).toFunctor.obj M ⟶
      (modulesPseudofunctor.map (tensorHMap3 R' V G A e c hV).op.toLoc).toFunctor.obj M :=
  pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
    (f₁ := projection1 (R := R) R' G) (f₂ := projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β).hom ((H (R := R) R' V G).ι ≫ chart23 R' V G A e c hV)
    (tensorHMap2 R' V G A e c hV) (tensorHMap3 R' V G A e c hV)
    (by simp only [tensorHMap2, Category.assoc])
    (by simpa only [tensorHMap3, Category.assoc] using congrArg ((H (R := R) R' V G).ι ≫ ·) (nerve_eq3 R' V G A e c hV).symm)

def tensorHLine13 :
    (modulesPseudofunctor.map (tensorHMap1 (R := R) R' V G).op.toLoc).toFunctor.obj M ⟶
      (modulesPseudofunctor.map (tensorHMap3 R' V G A e c hV).op.toLoc).toFunctor.obj M :=
  pullHom (F := modulesPseudofunctor) (M₁ := M) (M₂ := M)
    (f₁ := projection1 (R := R) R' G) (f₂ := projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β).hom ((H (R := R) R' V G).ι ≫ chart13 (R := R) R' G)
    (tensorHMap1 (R := R) R' V G) (tensorHMap3 R' V G A e c hV)
    (by simp only [tensorHMap1, Category.assoc]) (by simp only [tensorHMap3, Category.assoc])

/-- Actual generic 12 comparison through the SAME original line coordinate. -/
def tensorHCompare12 := genericLineCompare (modelGenericOpen R' V G).ι
  (genericModelOfGroupIso (baseMap R R') V G A e).q M L β
  (tensorHLift1 (R := R) R' V G) (tensorHLift2 R' V G A e c hV)
  (tensorHMap1 (R := R) R' V G) (tensorHMap2 R' V G A e c hV) (tensorHOriginalCoordinate R' V G A e)
  (tensorHLift1_model (R := R) R' V G) (tensorHLift2_model R' V G A e c hV) rfl
  (tensorHLift2_original R' V G A e c hV)

def tensorHCompare23 := genericLineCompare (modelGenericOpen R' V G).ι
  (genericModelOfGroupIso (baseMap R R') V G A e).q M L β
  (tensorHLift2 R' V G A e c hV) (tensorHLift3 R' V G A e c hV)
  (tensorHMap2 R' V G A e c hV) (tensorHMap3 R' V G A e c hV) (tensorHOriginalCoordinate R' V G A e)
  (tensorHLift2_model R' V G A e c hV) (tensorHLift3_model R' V G A e c hV)
  (tensorHLift2_original R' V G A e c hV) (tensorHLift3_original R' V G A e c hV)

def tensorHCompare13 := genericLineCompare (modelGenericOpen R' V G).ι
  (genericModelOfGroupIso (baseMap R R') V G A e).q M L β
  (tensorHLift1 (R := R) R' V G) (tensorHLift3 R' V G A e c hV)
  (tensorHMap1 (R := R) R' V G) (tensorHMap3 R' V G A e c hV) (tensorHOriginalCoordinate R' V G A e)
  (tensorHLift1_model (R := R) R' V G) (tensorHLift3_model R' V G A e c hV) rfl
  (tensorHLift3_original R' V G A e c hV)

theorem tensorHLine12_spec : tensorHLine12 R' V G A e c hV M L β =
    (tensorHCompare12 R' V G A e c hV M L β).hom :=
  tensorLineIso_on_generic_common R' V G A e c hV M L β (factor12 (R := R) R' V G) _
    (factor12_ι (R := R) R' V G) _ _ (shared_generic_first (R := R) R' V G)
    (shared_generic_middle R' V G A e c hV) _ _ _
    (by simpa only [tensorHMap1, Category.assoc] using congrArg ((H (R := R) R' V G).ι ≫ ·) (nerve_eq1 (R := R) R' G))
    (by simpa only [tensorHMap2, Category.assoc] using congrArg ((H (R := R) R' V G).ι ≫ ·) (nerve_eq2 R' V G A e c hV))
    (tensorHLift1_model (R := R) R' V G) (tensorHLift2_model R' V G A e c hV) rfl
    (tensorHLift2_original R' V G A e c hV)

theorem tensorHLine23_spec : tensorHLine23 R' V G A e c hV M L β =
    (tensorHCompare23 R' V G A e c hV M L β).hom :=
  tensorLineIso_on_generic_common R' V G A e c hV M L β (factor23 R' V G A e c hV) _
    (factor23_ι R' V G A e c hV) _ _ rfl (shared_generic_last R' V G A e c hV) _ _ _
    (by simp only [tensorHMap2, Category.assoc])
    (by simpa only [tensorHMap3, Category.assoc] using congrArg ((H (R := R) R' V G).ι ≫ ·) (nerve_eq3 R' V G A e c hV).symm)
    (tensorHLift2_model R' V G A e c hV) (tensorHLift3_model R' V G A e c hV)
    (tensorHLift2_original R' V G A e c hV) (tensorHLift3_original R' V G A e c hV)

theorem tensorHLine13_spec : tensorHLine13 R' V G A e c hV M L β =
    (tensorHCompare13 R' V G A e c hV M L β).hom :=
  tensorLineIso_on_generic_common R' V G A e c hV M L β (factor13 (R := R) R' V G) _
    (factor13_ι (R := R) R' V G) _ _ rfl rfl _ _ _
    (by simp only [tensorHMap1, Category.assoc]) (by simp only [tensorHMap3, Category.assoc])
    (tensorHLift1_model (R := R) R' V G) (tensorHLift3_model R' V G A e c hV) rfl
    (tensorHLift3_original R' V G A e c hV)

/-- The three original generic comparisons cancel at the SAME middle beta. -/
theorem tensorHCompare_cocycle : (tensorHCompare12 R' V G A e c hV M L β).hom ≫
    (tensorHCompare23 R' V G A e c hV M L β).hom = (tensorHCompare13 R' V G A e c hV M L β).hom :=
  genericLineCompare_cocycle (modelGenericOpen R' V G).ι (genericModelOfGroupIso (baseMap R R') V G A e).q M L β
    (tensorHLift1 (R := R) R' V G) (tensorHLift2 R' V G A e c hV) (tensorHLift3 R' V G A e c hV)
    (tensorHMap1 (R := R) R' V G) (tensorHMap2 R' V G A e c hV) (tensorHMap3 R' V G A e c hV)
    (tensorHOriginalCoordinate R' V G A e) (tensorHLift1_model (R := R) R' V G)
    (tensorHLift2_model R' V G A e c hV) (tensorHLift3_model R' V G A e c hV) rfl
    (tensorHLift2_original R' V G A e c hV) (tensorHLift3_original R' V G A e c hV)

/-- Literal native chosen-psi 12/23 composition equals 13 on the actual H open. -/
theorem tensorLineIso_triple_generic : tensorHLine12 R' V G A e c hV M L β ≫
    tensorHLine23 R' V G A e c hV M L β = tensorHLine13 R' V G A e c hV M L β :=
  Abstract.composition_of_comparisons
    (tensorHLine12 R' V G A e c hV M L β) (tensorHCompare12 R' V G A e c hV M L β).hom
    (tensorHLine23 R' V G A e c hV M L β) (tensorHCompare23 R' V G A e c hV M L β).hom
    (tensorHLine13 R' V G A e c hV M L β) (tensorHCompare13 R' V G A e c hV M L β).hom
    (tensorHLine12_spec R' V G A e c hV M L β) (tensorHLine23_spec R' V G A e c hV M L β)
    (tensorHLine13_spec R' V G A e c hV M L β) (tensorHCompare_cocycle R' V G A e c hV M L β)

#print axioms tensorLineIso_triple_generic

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
