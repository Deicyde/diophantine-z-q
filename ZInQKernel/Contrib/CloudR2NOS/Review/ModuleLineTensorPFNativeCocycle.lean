/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Original tensor-triple NATIVE nine-factor equality, stated in the common PF
coefficient category. The nine-factor and three-factor values are literal
native pullbackComp/pullbackCongr/mapIso constructions, and their equality is
proved from the actual global hom law, not a cocycle premise. Compatibility
with frozen ActualLineCocycle must be audited by WHOLE-type isDefEq.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorTripleCocycle
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorNativeCharts
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineNativeNinePrimitive
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineNativeThirdPrimitive
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineAbstractIsoHom

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
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

def tensorTriplePFNativeNine :=
  tensorTripleNative12 R' V G A e c hV M L β ≪≫ tensorTripleNative23 R' V G A e c hV M L β

def tensorTriplePFNativeThree := nativeThirdLineIso (X := G.X.1)
  M (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
  (tensorLineIso R' V G A e c hV M L β) (chart13 (R := R) R' G)

theorem tensorTriplePFNativeNine_hom :
    (tensorTriplePFNativeNine R' V G A e c hV M L β).hom =
      tensorTripleLine12 R' V G A e c hV M L β ≫ tensorTripleLine23 R' V G A e c hV M L β :=
  Abstract.iso_blocks_hom
    (D := modulesPseudofunctor.obj (.mk (op (model3 (R := R) R' G))))
    (tensorTripleNative12 R' V G A e c hV M L β)
    (tensorTripleNative23 R' V G A e c hV M L β)
    (tensorTripleLine12 R' V G A e c hV M L β)
    (tensorTripleLine23 R' V G A e c hV M L β)
    (tensorTripleNative12_hom R' V G A e c hV M L β)
    (tensorTripleNative23_hom R' V G A e c hV M L β)

theorem tensorTriplePFNativeThree_hom :
    (tensorTriplePFNativeThree R' V G A e c hV M L β).hom = tensorTripleLine13 R' V G A e c hV M L β :=
  nativeThirdLineIso_hom (X := G.X.1)
    M (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β) (chart13 (R := R) R' G)

/-- Actual native nine-factor equality from the PROVED original global hom law. -/
theorem tensorLineIso_nativeNineFactor_eq :
    tensorTriplePFNativeNine R' V G A e c hV M L β =
      tensorTriplePFNativeThree R' V G A e c hV M L β :=
  Abstract.iso_eq_of_common_hom
    (D := modulesPseudofunctor.obj (.mk (op (model3 (R := R) R' G))))
    (tensorTriplePFNativeNine R' V G A e c hV M L β)
    (tensorTriplePFNativeThree R' V G A e c hV M L β)
    (tensorTripleLine13 R' V G A e c hV M L β)
    (Abstract.hom_eq_of_normalization _ _ _
      (tensorTriplePFNativeNine_hom R' V G A e c hV M L β)
      (tensorLineIso_triple_hom_cocycle R' V G A e c hV M L β))
    (tensorTriplePFNativeThree_hom R' V G A e c hV M L β)

#print axioms tensorLineIso_nativeNineFactor_eq

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
