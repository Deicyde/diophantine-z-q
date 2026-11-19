/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

The actual chosen tensor line map, on any test factoring through its ORIGINAL
generic open, equals conjugation through the original native line beta.
No generic-coordinate scalar, global hpsi, ampleness or extension is assumed.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorTests
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineAbstractGenericChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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

/-- The prescribed original generic chart map, pulled along an ACTUAL test. -/
theorem tensorLineIso_on_generic_factor {T : Scheme.{u}}
    (r : T ⟶ (modelSquareGenericOpen R' V G).toScheme)
    (t : T ⟶ model2 (R := R) R' G)
    (hrt : r ≫ (modelSquareGenericOpen R' V G).ι = t)
    (x y : T ⟶ G.X.left)
    (hx : t ≫ projection1 (R := R) R' G = x)
    (hy : t ≫ projection2 R' V G A e c hV = y) :
    let i := (modelGenericOpen R' V G).ι
    let q := (genericModelOfGroupIso (baseMap R R') V G A e).q
    let a := genericProjection1 R' V G
    let b := genericProjection2 R' V G A e c hV
    pullHom (F := modulesPseudofunctor) (tensorLineIso R' V G A e c hV M L β).hom
        t x y hx hy =
      (genericLineCompare i q M L β (r ≫ a) (r ≫ b) x y (r ≫ (a ≫ q))
        (by rw [Category.assoc, genericProjection1_ι, ← Category.assoc, hrt, hx])
        (by rw [Category.assoc, genericProjection2_ι, ← Category.assoc, hrt, hy])
        (by rw [Category.assoc])
        (by rw [Category.assoc, ← genericCoordinate_invariant])).hom := by
  dsimp only []
  rw [genericLineCompare_hom]
  exact Abstract.pullHom_of_conjugated_chart (F := modulesPseudofunctor)
    (modelGenericOpen R' V G).ι (genericModelOfGroupIso (baseMap R R') V G A e).q β
    (projection1 (R := R) R' G) (projection2 R' V G A e c hV)
    (modelSquareGenericOpen R' V G).ι
    (genericProjection1 R' V G) (genericProjection2 R' V G A e c hV)
    (genericProjection1_ι R' V G) (genericProjection2_ι R' V G A e c hV)
    (genericCoordinate_invariant R' V G A e c hV)
    (tensorLineIso R' V G A e c hV M L β).hom
    (by
      rw [← genericLineCompare_hom, ← iteratedLineIso_hom]
      exact tensorLineIso_generic R' V G A e c hV M L β)
    r t hrt x y hx hy

#print axioms tensorLineIso_on_generic_factor

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
