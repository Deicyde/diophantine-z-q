import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffineGammaLRS

/-!
# Actual complex-constant compatibility of an affine analytification comparison

A genuine LRS comparison over the exact lifted complex base induces an actual
complex-preserving regular-ring pullback. Γ–Spec injectivity proves the ring
identity from the true over-base square; no compatibility structure is assumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (Y : Over (Spec (CommRingCat.of ℂ))) (e : ℕ) [SmoothOfRelativeDimension e Y.hom]
variable (q : ComplexPoint Y)

local instance affineComparisonTarget : IsAffine (actualEtaleNativeScheme Y e q).left :=
  (actualEtaleDatum Y e q).isAffine

/-- The original affine scheme's actual lifted structure morphism is its real Γ–Spec constant map. -/
theorem actualEtaleLRS_structure_as_toSpec :
    (actualEtaleNativeScheme Y e q).left.toLocallyRingedSpace.toSpecOfAlgMap
      (uliftAlgMap (actualEtaleNativeConst Y e q)) =
        (overULift (actualEtaleNativeScheme Y e q)).hom.toLRSHom := by
  let V := actualEtaleNativeScheme Y e q
  let E := asIso V.left.toSpecΓ
  have h := congrArg Scheme.Hom.toLRSHom (actualEtaleFromSpecΓ_overULift Y e q)
  have he : E.hom.toLRSHom ≫ E.inv.toLRSHom = 𝟙 _ :=
    congrArg Scheme.Hom.toLRSHom E.hom_inv_id
  calc
    _ = E.hom.toLRSHom ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom (uliftAlgMap (actualEtaleNativeConst Y e q))) := rfl
    _ = E.hom.toLRSHom ≫ (E.inv.toLRSHom ≫ (overULift V).hom.toLRSHom) :=
      congrArg (fun f => E.hom.toLRSHom ≫ f) h.symm
    _ = (E.hom.toLRSHom ≫ E.inv.toLRSHom) ≫ (overULift V).hom.toLRSHom :=
      (Category.assoc _ _ _).symm
    _ = (overULift V).hom.toLRSHom :=
      (congrArg (fun f => f ≫ (overULift V).hom.toLRSHom) he).trans (Category.id_comp _)

/-- The actual comparison's regular-ring pullback preserves the original complex constants. -/
theorem affineComparison_gamma_constants (Z : AnalyticSpace)
    (f : Z.toLocallyRingedSpace ⟶ (actualEtaleNativeScheme Y e q).left.toLocallyRingedSpace)
    (hbase : f ≫ (overULift (actualEtaleNativeScheme Y e q)).hom.toLRSHom = Z.toSpecℂ) (c : ℂ) :
    (LocallyRingedSpace.Γ.map f.op).hom (actualEtaleNativeConst Y e q c) = Z.algebraMap c := by
  have H : Z.toLocallyRingedSpace.toSpecOfAlgMap
      (LocallyRingedSpace.comapAlgMap f (uliftAlgMap (actualEtaleNativeConst Y e q))) = Z.toSpecℂ :=
    (LocallyRingedSpace.comp_toSpecOfAlgMap f (uliftAlgMap (actualEtaleNativeConst Y e q))).symm.trans
      ((congrArg (fun g => f ≫ g) (actualEtaleLRS_structure_as_toSpec Y e q)).trans hbase)
  have H' : LocallyRingedSpace.comapAlgMap f (uliftAlgMap (actualEtaleNativeConst Y e q)) =
      uliftAlgMap Z.algebraMap :=
    LocallyRingedSpace.toSpecOfAlgMap_injective Z.toLocallyRingedSpace H
  exact RingHom.congr_fun H' (ULift.up c)

end ZInQ.Contrib.CloudB3W17bOkaComparison
