import ZInQKernel.Contrib.CloudB3W17bOkaComparison.AffinePullbackLaw
import ZInQKernel.Contrib.CloudB3W17bOkaComparison.UnramifiedResidueAgreement

/-!
# Genuine local inverse uniqueness for the ACTUAL canonical algebraic étale chart

The finite-type/formally-unramified algebra is derived internally from the real
Hodge coordinateRingHomOnOpen_etale, not supplied by a replacement chart.
Actual coordinate-base and residue agreement imply equality of actual LRS maps
into the original affine neighbourhood. This is the algebraic uniqueness step
of the native/Oka local inverse, not an algebraicity premise for F/H.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite ComplexAnalytic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bOkaComparison

variable (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
variable (p : ComplexPoint X)

local instance canonicalChartAffine : IsAffine (actualEtaleNativeScheme X d p).left :=
  (actualEtaleDatum X d p).isAffine

/-- The REAL canonical algebraic étale coordinate ring supplies the actual LRS uniqueness.
The hypotheses are ordinary coordinate and genuine stalk-residue equalities to be proved
on the chosen analytic neighbourhood; no map/model/GAGA witness is assumed. -/
theorem actualEtale_residue_lrs_hom_ext (Z : LocallyRingedSpace.{0})
    (f g : Z ⟶ (actualEtaleNativeScheme X d p).left.toLocallyRingedSpace)
    (hcoords : (LocallyRingedSpace.Γ.map f.op).hom.comp
        (actualEtaleDatum X d p).coordinateRingHomOnOpen =
      (LocallyRingedSpace.Γ.map g.op).hom.comp
        (actualEtaleDatum X d p).coordinateRingHomOnOpen)
    (v : ∀ z : Z, Z.presheaf.stalk z →+* ℂ) [∀ z, IsLocalHom (v z)]
    (hvalues : ∀ (z : Z) r,
      v z (Z.presheaf.Γgerm z ((LocallyRingedSpace.Γ.map f.op).hom r)) =
        v z (Z.presheaf.Γgerm z ((LocallyRingedSpace.Γ.map g.op).hom r))) : f = g := by
  let D := actualEtaleDatum X d p
  letI : Algebra (MvPolynomial (Fin d) ℂ)
      (LocallyRingedSpace.Γ.obj (op (actualEtaleNativeScheme X d p).left.toLocallyRingedSpace)) :=
    D.coordinateRingHomOnOpen.toAlgebra
  letI : Algebra.Etale (MvPolynomial (Fin d) ℂ)
      (LocallyRingedSpace.Γ.obj (op (actualEtaleNativeScheme X d p).left.toLocallyRingedSpace)) :=
    RingHom.etale_algebraMap.mp D.coordinateRingHomOnOpen_etale
  have hb : (LocallyRingedSpace.Γ.map f.op).hom.comp
      (algebraMap (MvPolynomial (Fin d) ℂ)
        (LocallyRingedSpace.Γ.obj (op (actualEtaleNativeScheme X d p).left.toLocallyRingedSpace))) =
    (LocallyRingedSpace.Γ.map g.op).hom.comp
      (algebraMap (MvPolynomial (Fin d) ℂ)
        (LocallyRingedSpace.Γ.obj (op (actualEtaleNativeScheme X d p).left.toLocallyRingedSpace))) := hcoords
  have H := unramified_residue_all_points_maps_ext Z
    (LocallyRingedSpace.Γ.map f.op).hom (LocallyRingedSpace.Γ.map g.op).hom hb v hvalues
  exact affine_lrs_hom_ext (actualEtaleNativeScheme X d p).left Z f g H

end ZInQ.Contrib.CloudB3W17bOkaComparison
