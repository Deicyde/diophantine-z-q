import ZInQKernel.Contrib.OneProof.EllAdic.ConstantResidueCohomologyTorsionV1
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleResidueHOneForwardV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

namespace RC53.EllAdic

universe u

local instance residueTorsionEtaleSheafify (S : Scheme.{u}) :
    HasSheafify S.smallEtaleTopology Ab.{u+1} := inferInstance

local instance residueTorsionEtaleGrothendieck (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u+1} (Sheaf S.smallEtaleTopology Ab.{u+1}) := by
  let : EssentiallySmall.{u+1} S.Etale := inferInstance
  exact Sheaf.isGrothendieckAbelian_of_essentiallySmall S.smallEtaleTopology Ab.{u+1}

local instance residueTorsionEtaleExt (S : Scheme.{u}) :
    HasExt.{u+1} (Sheaf S.smallEtaleTopology Ab.{u+1}) :=
  IsGrothendieckAbelian.hasExt (Sheaf S.smallEtaleTopology Ab.{u+1})

/-- The specified degree-one étale group is killed by the modulus of the
literal residue sheaf. No module instance on the cohomology group is used. -/
theorem etaleConstantResidue_hOne_nsmul_eq_zero (S : Scheme.{u}) (p n : ℕ)
    (x : ((etaleConstantResidue S p n).H 1 : Type (u+1))) :
    (p ^ n : ℕ) • x = 0 :=
  liftedZMod_constantSheaf_cohomology_nsmul_eq_zero S.smallEtaleTopology (p ^ n) 1 x

end RC53.EllAdic
