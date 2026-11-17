/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Actual original 12/23 native isos, obtained by specializing the PF-carrier
primitives checked separately in generic X/Y/Z. No native-nineFactor_hom
carrier conversion or concrete unfolding of native iso proof fields is used.
No cocycle/VA/NOS premise or kernel budget change.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorTripleCocycle
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineNativeChartPrimitive

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
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

def tensorTripleNative12 := nativeDirectLineIso (X := G.X.1)
  M (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
  (tensorLineIso R' V G A e c hV M L β) (chart12 (R := R) R' G)
  (tensorTripleMap1 (R := R) R' G) (tensorTripleMap2 R' V G A e c hV)
  (nerve_eq1 (R := R) R' G) (nerve_eq2 R' V G A e c hV)

def tensorTripleNative23 := nativeSecondLineIso (X := G.X.1)
  M (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
  (tensorLineIso R' V G A e c hV M L β) (chart23 R' V G A e c hV)
  (tensorTripleMap3 R' V G A e c hV) (nerve_eq3 R' V G A e c hV)

theorem tensorTripleNative12_hom :
    (tensorTripleNative12 R' V G A e c hV M L β).hom = tensorTripleLine12 R' V G A e c hV M L β :=
  nativeDirectLineIso_hom (X := G.X.1)
    M (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β) (chart12 (R := R) R' G)
    (tensorTripleMap1 (R := R) R' G) (tensorTripleMap2 R' V G A e c hV)
    (nerve_eq1 (R := R) R' G) (nerve_eq2 R' V G A e c hV)

theorem tensorTripleNative23_hom :
    (tensorTripleNative23 R' V G A e c hV M L β).hom = tensorTripleLine23 R' V G A e c hV M L β :=
  nativeSecondLineIso_hom (X := G.X.1)
    M (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β) (chart23 R' V G A e c hV)
    (tensorTripleMap3 R' V G A e c hV) (nerve_eq3 R' V G A e c hV)

#print axioms tensorTripleNative12_hom
#print axioms tensorTripleNative23_hom

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
