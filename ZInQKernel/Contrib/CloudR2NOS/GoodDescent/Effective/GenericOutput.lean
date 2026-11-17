/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

ACTUAL generic scheme comparison on the SAME effective descended output.
Both the map and inverse are constructed by fpqc morphism descent of the
same original generic coordinate. Generic coequalizer invariance is proved
from the already constructed original transport, never supplied as hdesc.
This intermediate is upgraded to a GROUP iso separately; it is not a
scheme-only replacement for HasGoodReduction or a NOS proof.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GenericTensor
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.ComparisonIso

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
open TensorCofaces TensorNerve

/-- Construct the generic comparison of an actual effective output with
    the SAME original generic A. No generic-output iso is a premise. -/
theorem exists_genericSchemeIso_on_effective_output
    {R : Type u} [CommRing R] (R' : Type u) [CommRing R'] [Algebra R R']
    [Module.FaithfullyFlat R R'] (V : (Base R).Opens)
    (G : Grp (Over (Cover R'))) (A : Grp (Over V.toScheme))
    (e : (Over.pullback ((baseMap R R') ⁻¹ᵁ V).ι).mapGrp.obj G ≅
      (Over.pullback ((baseMap R R') ∣_ V)).mapGrp.obj A)
    [Etale (baseMap R R')] (c : Base R)
    [Mono ((baseMap R R').fiberToSpecResidueField c)]
    (hV : ∀ z : Base R, z ∉ V → z = c)
    (D : Grp (Over (Base R))) (q : G.X.left ⟶ D.X.left)
    (hq : IsPullback q G.X.hom D.X.hom (baseMap R R'))
    (hco : projection1 (R := R) R' G ≫ q = projection2 R' V G A e c hV ≫ q) :
    ∃ i : (D.X.hom ⁻¹ᵁ V).toScheme ≅ A.X.left,
      genericCartMap hq V ≫ i.hom = (genericModelOfGroupIso (baseMap R R') V G A e).q ∧
      i.hom ≫ A.X.hom = D.X.hom ∣_ V := by
  let M := genericModelOfGroupIso (baseMap R R') V G A e
  let W := D.X.hom ⁻¹ᵁ V
  let qg := genericCartMap hq V
  let a₁ := genericProjection1 R' V G
  let a₂ := genericProjection2 R' V G A e c hV
  have hcoG : a₁ ≫ qg = a₂ ≫ qg := by
    apply (cancel_mono W.ι).mp
    calc
      (a₁ ≫ qg) ≫ W.ι = (modelSquareGenericOpen R' V G).ι ≫
          (projection1 (R := R) R' G ≫ q) := by
        rw [Category.assoc, genericCartMap_ι, ← Category.assoc, genericProjection1_ι, Category.assoc]
      _ = (modelSquareGenericOpen R' V G).ι ≫ (projection2 R' V G A e c hV ≫ q) :=
        congrArg ((modelSquareGenericOpen R' V G).ι ≫ ·) hco
      _ = (a₂ ≫ qg) ≫ W.ι := by
        symm
        dsimp only [a₂]
        rw [Category.assoc, genericCartMap_ι, ← Category.assoc, genericProjection2_ι, Category.assoc]
  obtain ⟨i, hi, hiInv, hb⟩ := exists_comparisonIso_of_fpqc_coequalizers
    (W.ι ≫ D.X.hom) (A.X.hom ≫ V.ι) (genericStructure1 R' V G) qg M.q
    (genericCart_isPullback hq V) (originalGenericModel_isPullback_ambient (baseMap R R') V G A e)
    (genericStructure2 R' V G) a₁ a₂ (genericCartesian1 R' V G) (genericCartesian2 R' V G A e c hV)
    hcoG (genericCoordinate_invariant R' V G A e c hV)
  have he : i.hom ≫ A.X.hom = D.X.hom ∣_ V := by
    apply (cancel_mono V.ι).mp
    simpa only [Category.assoc] using hb.trans (morphismRestrict_ι D.X.hom V).symm
  exact ⟨i, hi, he⟩

#print axioms exists_genericSchemeIso_on_effective_output

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
