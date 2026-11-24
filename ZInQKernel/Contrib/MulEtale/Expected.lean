import ZInQKernel.HDecomp.Objects

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.MulEtale.Expected

/-- Independent literal of the fixed arbitrary-base H-101 contract. -/
def target : Prop :=
  ∀ (O : Type) [CommRing O]
    (A : Grp (Over (Spec (.of O)))) [PkgI2.IsAbelianScheme A] (m : ℕ),
    IsUnit (m : O) → Etale ((𝟙 A.X ^ m : A.X ⟶ A.X).left)

end ZInQ.Contrib.MulEtale.Expected
