/-
Multiplication-etale construction: OriginNeighbourhood.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.LocalPromotion
import ZInQKernel.Contrib.MulEtale.Direct.ActualOriginFormalEtale

noncomputable section

open CategoryTheory AlgebraicGeometry
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace H101DirectFieldRoute.LocalPromotion

universe u

/-- Source-only actual call-site join: an invertible natural scalar yields an
actual affine etale neighbourhood of the original identity, using the genuine
upstream actual-stalk proof and the independent local-promotion proof.
No Flat/Etale/formal-etale/bijection or chart premise is added to the field inputs. -/
theorem exists_etale_open_mul_at_unit_of_isUnit
    (k : Type u) [Field k] (G : Over (Spec (.of k))) [GrpObj G] [Smooth G.hom]
    (m : ℕ) (hm : IsUnit (m : k)) (s : Spec (.of k)) :
    ∃ V : G.left.Opens, IsAffineOpen V ∧ η[G].left s ∈ V ∧
      Etale (V.ι ≫ (𝟙 G ^ m : G ⟶ G).left) := by
  exact exists_etale_open_mul_at_unit G m s
    (H101DirectFieldRoute.ActualTransport.unit_actualStalkMap_formallyEtale k G m hm s)

end H101DirectFieldRoute.LocalPromotion
