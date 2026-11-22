/-
Multiplication-etale construction: FieldMulEtale.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.OriginNeighbourhood
import ZInQKernel.Contrib.MulEtale.Direct.FieldTranslationDescent

noncomputable section

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace H101DirectFieldRoute.Translation

universe u

/-- **Field helper (source).** For the ORIGINAL field `k` and the actual smooth, proper,
geometrically integral group `G` over `Spec k`, multiplication by every `m : ℕ` with
`IsUnit (m : k)` is étale.  `m = 0` is not excluded by an extra hypothesis: `IsUnit (0 : k)` is
false in a field, so that case is vacuous through the given hypothesis itself.  Commutativity is
derived inside from native `isCommMonObj_of_isProper_of_geometricallyIntegral`. -/
theorem etale_pow_id_left_of_isUnit {k : Type u} [Field k]
    (G : Over (Spec (.of k))) [GrpObj G] [Smooth G.hom] [IsProper G.hom]
    [GeometricallyIntegral G.hom] (m : ℕ) (hm : IsUnit (m : k)) :
    Etale ((𝟙 G ^ m : G ⟶ G).left) :=
  etale_pow_id_left_of_etale_unit_nbhd G m (IsLocalRing.closedPoint k)
    (H101DirectFieldRoute.LocalPromotion.exists_etale_open_mul_at_unit_of_isUnit k G m hm
      (IsLocalRing.closedPoint k))

end H101DirectFieldRoute.Translation
