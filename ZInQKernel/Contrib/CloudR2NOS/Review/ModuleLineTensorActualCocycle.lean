/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Prescribed NATIVE NINE-FACTOR ActualLineCocycle on the original TensorTriple.
The global hom equality is PROVED from actual D/H tests, not supplied as an
extra premise. M/L/beta are explicit line inputs; this is not M existence,
relative very-ampleness, model existence, or a final NOS theorem.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorPFNativeCocycle
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineNativeBlockConversion
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.ProjConstruction

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

/-- The chosen actual native tensor-square line iso satisfies the EXACT
nine-factor cocycle used by the frozen original effective-descent consumer. -/
theorem tensorLineIso_actualLineCocycle
    {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
    (V : (Base R).Opens) (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
    (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
      (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
    [Etale (baseMap R R')] (c : Base R)
    [Mono ((baseMap R R').fiberToSpecResidueField c)]
    (hV : ∀ z : Base R, z ∉ V → z = c)
    (M : G.X.left.Modules) (L : A.X.left.Modules)
    (β : (Scheme.Modules.pullback (modelGenericOpen R' V G).ι).obj M ≅
      (Scheme.Modules.pullback (genericModelOfGroupIso (baseMap R R') V G A e).q).obj L) :
    ActualLineCocycle R' V G A e c hV M (tensorLineIso R' V G A e c hV M L β) := by
  unfold ActualLineCocycle
  exact nativeNineFactor_of_blockIso (X := G.X.1)
    (Y := model2 (R := R) R' G) (Z := model3 (R := R) R' G)
    M (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β)
    (chart12 (R := R) R' G) (chart13 (R := R) R' G) (chart23 R' V G A e c hV)
    (nerve_eq1 (R := R) R' G) (nerve_eq2 R' V G A e c hV)
    (nerve_eq3 R' V G A e c hV)
    (tensorLineIso_nativeNineFactor_eq R' V G A e c hV M L β)

#print axioms tensorLineIso_actualLineCocycle

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
