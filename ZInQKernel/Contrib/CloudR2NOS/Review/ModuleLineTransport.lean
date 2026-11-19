/-
Copyright (c) 2026 H5/NOS Round-2 Lane6 contributors.
Released under the Apache License, Version 2.0.

New SPECIFIC diagonal/generic GIVEN-line adapter. It constructs compatibility
of pullbacks of the GIVEN full-model line M from one GIVEN generic-line iso β
with the ORIGINAL generic line L. Compatibility on the overlap is PROVED by
actual equal generic lifts on the diagonal and cancellation through β, not
passed as hdescLine, Pic uniqueness, a cube, or scalar-extension Fact.

Inputs D/H cover, diagonal equality, and generic coordinate maps are actual
scheme-morphism data provided by Lane5's frozen transport. M/β are explicit
INTERMEDIATE inputs, not an actual generic ample-line extension/model-existence
proof. Scheme.Modules is the native coefficient type; no nominal substitution
for a custom OModulePresheaf is claimed. Arbitrary scheme universe/characteristic.
-/
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineComparison
import ZInQKernel.Contrib.CloudR2NOS.Review.ModuleLineAbstractOverlap

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Pseudofunctor
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace ZInQ.Contrib.CloudR2NOS.Review.LineDescent

/-- ACTUAL line compatibility from the diagonal/generic cover. Unlike the
primitive gluing theorem, NO overlap-line-compatibility hypothesis is supplied. -/
theorem exists_lineIso_diagonal_generic
    {X Xg A T : Scheme.{u}} (i : Xg ⟶ X) [Mono i] (q : Xg ⟶ A)
    (M : modulesPseudofunctor.obj (.mk (op X)))
    (L : modulesPseudofunctor.obj (.mk (op A)))
    (β : (modulesPseudofunctor.map i.op.toLoc).toFunctor.obj M ≅
      (modulesPseudofunctor.map q.op.toLoc).toFunctor.obj L)
    (x y : T ⟶ X) (D H : T.Opens) (hDH : D ⊔ H = ⊤)
    (hD : D.ι ≫ x = D.ι ≫ y)
    (a b : H.toScheme ⟶ Xg) (hx : a ≫ i = H.ι ≫ x) (hy : b ≫ i = H.ι ≫ y)
    (hq : a ≫ q = b ≫ q) :
    let δD := coefficientEqIso M hD
    let δH := genericLineCompare i q M L β a b (H.ι ≫ x) (H.ι ≫ y) (a ≫ q)
      hx hy rfl hq.symm
    ∃ E : (modulesPseudofunctor.map x.op.toLoc).toFunctor.obj M ≅
        (modulesPseudofunctor.map y.op.toLoc).toFunctor.obj M,
      (modulesPseudofunctor.map D.ι.op.toLoc).toFunctor.map E.hom =
        (iteratedLineIso M x y D.ι δD).hom ∧
      (modulesPseudofunctor.map H.ι.op.toLoc).toFunctor.map E.hom =
        (iteratedLineIso M x y H.ι δH).hom := by
  let δD := coefficientEqIso M hD
  let δH := genericLineCompare i q M L β a b (H.ι ≫ x) (H.ι ≫ y) (a ≫ q)
    hx hy rfl hq.symm
  apply exists_iso_twoOpen D H hDH
    ((modulesPseudofunctor.map x.op.toLoc).toFunctor.obj M)
    ((modulesPseudofunctor.map y.op.toLoc).toFunctor.obj M)
    (iteratedLineIso M x y D.ι δD) (iteratedLineIso M x y H.ι δH)
  intro T' r d h hdr hhr
  rw [iteratedLineIso_hom, iteratedLineIso_hom, genericLineCompare_hom]
  exact Abstract.twoMapComparisons_compatible (F := modulesPseudofunctor)
    i q β x y D.ι H.ι hD a b hx hy hq r d h hdr hhr

#print axioms exists_lineIso_diagonal_generic

end ZInQ.Contrib.CloudR2NOS.Review.LineDescent
