/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

Restate the proved generic-chart restriction with explicitly shared generic
lifts and an explicitly shared ORIGINAL variety coordinate. The input map
identities are scheme geometry, not a desired line-cocycle conclusion.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineTensorGenericTests
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineAbstractRetarget

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

/-- A generic test is conjugation through these ACTUAL common lifts/coordinate. -/
theorem tensorLineIso_on_generic_common {T : Scheme.{u}}
    (r : T ⟶ (modelSquareGenericOpen R' V G).toScheme)
    (t : T ⟶ model2 (R := R) R' G)
    (hrt : r ≫ (modelSquareGenericOpen R' V G).ι = t)
    (a b : T ⟶ (modelGenericOpen R' V G).toScheme)
    (hra : r ≫ genericProjection1 R' V G = a)
    (hrb : r ≫ genericProjection2 R' V G A e c hV = b)
    (x y : T ⟶ G.X.left) (z : T ⟶ A.X.left)
    (hx : t ≫ projection1 (R := R) R' G = x)
    (hy : t ≫ projection2 R' V G A e c hV = y)
    (hax : a ≫ (modelGenericOpen R' V G).ι = x)
    (hby : b ≫ (modelGenericOpen R' V G).ι = y)
    (haz : a ≫ (genericModelOfGroupIso (baseMap R R') V G A e).q = z)
    (hbz : b ≫ (genericModelOfGroupIso (baseMap R R') V G A e).q = z) :
    pullHom (F := modulesPseudofunctor)
        (f₁ := projection1 (R := R) R' G) (f₂ := projection2 R' V G A e c hV)
        (M₁ := M) (M₂ := M) (tensorLineIso R' V G A e c hV M L β).hom
        t x y hx hy =
      (genericLineCompare (modelGenericOpen R' V G).ι
        (genericModelOfGroupIso (baseMap R R') V G A e).q M L β
        a b x y z hax hby haz hbz).hom := by
  have h := tensorLineIso_on_generic_factor R' V G A e c hV M L β r t hrt x y hx hy
  dsimp only [] at h
  rw [genericLineCompare_hom] at h ⊢
  have hz : r ≫ (genericProjection1 R' V G ≫
      (genericModelOfGroupIso (baseMap R R') V G A e).q) = z := by
    rw [← Category.assoc, hra, haz]
  exact h.trans (Abstract.conjugatedComparisons_retarget
    (F := modulesPseudofunctor) (modelGenericOpen R' V G).ι
    (genericModelOfGroupIso (baseMap R R') V G A e).q β
    (r ≫ genericProjection1 R' V G) (r ≫ genericProjection2 R' V G A e c hV)
    a b x y (r ≫ (genericProjection1 R' V G ≫
      (genericModelOfGroupIso (baseMap R R') V G A e).q)) z
    (by rw [Category.assoc, genericProjection1_ι, ← Category.assoc, hrt, hx])
    (by rw [Category.assoc, genericProjection2_ι, ← Category.assoc, hrt, hy])
    (by rw [Category.assoc])
    (by rw [Category.assoc, ← genericCoordinate_invariant])
    hax hby haz hbz hra hrb hz)

#print axioms tensorLineIso_on_generic_common

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
