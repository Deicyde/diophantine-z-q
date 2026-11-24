import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.RankOneTorus
import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.RingTheory.Localization.Submodule

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory

namespace ZInQ.ToricOrthogonality

/-- The product of the punctured affine line with the geometrically integral
special group is integral. -/
theorem isIntegral_product_puncturedLine {k : Type} [Field k] (H : Over (Spec (.of k)))
    [GeometricallyIntegral H.hom] [Flat H.hom] [UniversallyOpen H.hom] :
    IsIntegral (H ⊗ puncturedLine k).left := by
  let B := Localization.Away (Polynomial.X : Polynomial k)
  have : IsDomain B := IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (Polynomial.X_ne_zero (R := k)))
  have hDom : IsIntegral (puncturedLine k).left :=
    inferInstanceAs (IsIntegral (Spec (.of B)))
  have hNoeth : IsLocallyNoetherian (puncturedLine k).left :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of B)))
  exact inferInstanceAs (IsIntegral (pullback H.hom (puncturedLine k).hom))

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.isIntegral_product_puncturedLine
