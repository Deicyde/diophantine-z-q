import ZInQKernel.Contrib.OneProof.EllAdic.PadicProEtSheafLimitV1
import ZInQKernel.Contrib.OneProof.EllAdic.TowerProductKernelV2
import Mathlib.Algebra.Category.Grp.Limits

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace RC53.EllAdic

universe u

/-- The coefficient sheaf in the original cohomology universe. -/
noncomputable abbrev liftedPadicCoefficientSheaf (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    Sheaf (Scheme.ProEt.topology S) Ab.{u+1} :=
  (sheafCompose (Scheme.ProEt.topology S) AddCommGrpCat.uliftFunctor.{u+1}).obj
    (S.ellAdicSheaf p)

/-- The product of the actual finite residue sheaves. -/
noncomputable abbrev finiteResidueProEtProduct (S : Scheme.{u}) (p : ℕ) :
    Sheaf (Scheme.ProEt.topology S) Ab.{u+1} :=
  ∏ᶜ towerObjects (liftedFiniteResidueProEtSheafTower S p)

/-- The map into the product defined by the original residue reductions. -/
noncomputable def padicCoefficientToResidueProduct (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    liftedPadicCoefficientSheaf S p ⟶ finiteResidueProEtProduct S p :=
  towerConeToProduct _ (continuousResidueProEtSheafCone S p)

/-- The difference operator on the same lifted finite residue sheaves. -/
noncomputable def finiteResidueProEtSubShift (S : Scheme.{u}) (p : ℕ) :
    finiteResidueProEtProduct S p ⟶ finiteResidueProEtProduct S p :=
  towerSubShift (liftedFiniteResidueProEtSheafTower S p)

lemma padicCoefficientToResidueProduct_π (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] (n : ℕ) :
    padicCoefficientToResidueProduct S p ≫
      Pi.π (towerObjects (liftedFiniteResidueProEtSheafTower S p)) n =
        (continuousResidueProEtSheafCone S p).π.app (op n) :=
  towerConeToProduct_π _ _ n

lemma padicCoefficientToResidueProduct_comp_subShift (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    padicCoefficientToResidueProduct S p ≫ finiteResidueProEtSubShift S p = 0 :=
  towerConeToProduct_subShift _ (continuousResidueProEtSheafCone S p)

/-- The actual lifted p-adic coefficient sheaf is the kernel of the product
shift difference, using the original reductions as its coordinate maps. -/
noncomputable def padicCoefficientIsKernelOfSubShift (S : Scheme.{u}) (p : ℕ) [Fact p.Prime] :
    IsLimit (KernelFork.ofι (padicCoefficientToResidueProduct S p)
      (padicCoefficientToResidueProduct_comp_subShift S p)) :=
  towerLimitIsKernel _ (continuousResidueProEtSheafCone S p)
    (continuousResidueProEtSheafConeIsLimit S p)

end RC53.EllAdic
