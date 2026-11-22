import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.SeventhStalkConstruction.Prelude

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory TensorProduct"
h77_open "TensorProduct"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped _root_.TensorProduct

universe u
theorem native_fraction_lift_construction
    (R K S O : Type u)
    [rR : CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [kK : Field K] [aRK : Algebra R K] [IsFractionRing R K]
    [rS : CommRing S] [IsDomain S] [rO : CommRing O] [IsDomain O]
    [aRS : Algebra R S] [aRO : Algebra R O] [aSO : Algebra S O]
    (hRSO : IsScalarTower R S O)
    (ϖ : R) (hϖirr : Irreducible ϖ)
    (hinjRO : Function.Injective (algebraMap R O))
    (hinjRS : Function.Injective (algebraMap R S))
    (hinjSO : Function.Injective (algebraMap S O)) :
    ∃ (aKF : Algebra K (FractionRing O))
      (aKKprime : Algebra K (FractionRing S))
      (aKprimeF : Algebra (FractionRing S) (FractionRing O)),
      letI : Algebra K (FractionRing O) := aKF;
      letI : Algebra K (FractionRing S) := aKKprime;
      letI : Algebra (FractionRing S) (FractionRing O) := aKprimeF;
      FaithfulSMul R (FractionRing O) ∧ FaithfulSMul R (FractionRing S) ∧
      FaithfulSMul S (FractionRing O) ∧
      IsScalarTower R S (FractionRing S) ∧ IsScalarTower R O (FractionRing O) ∧
      IsScalarTower S O (FractionRing O) ∧ IsScalarTower R S (FractionRing O) ∧
      IsScalarTower R K (FractionRing O) ∧ IsScalarTower R K (FractionRing S) ∧
      IsScalarTower S (FractionRing S) (FractionRing O) ∧
      IsScalarTower R (FractionRing S) (FractionRing O) ∧
      IsScalarTower K (FractionRing S) (FractionRing O) := by
  letI : IsScalarTower R S O := hRSO
  haveI hRSKprime : IsScalarTower R S (FractionRing S) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hROF : IsScalarTower R O (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hSOF : IsScalarTower S O (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI hRSF : IsScalarTower R S (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      rw [IsScalarTower.algebraMap_apply S O (FractionRing O),
        IsScalarTower.algebraMap_apply R O (FractionRing O),
        ← IsScalarTower.algebraMap_apply R S O])
  haveI faithfulRF : FaithfulSMul R (FractionRing O) :=
    (faithfulSMul_iff_algebraMap_injective R (FractionRing O)).mpr (by
      rw [IsScalarTower.algebraMap_eq R O (FractionRing O)]
      exact (IsFractionRing.injective O (FractionRing O)).comp hinjRO)
  letI algKF : Algebra K (FractionRing O) :=
    (IsFractionRing.lift (g := algebraMap R (FractionRing O))
      (FaithfulSMul.algebraMap_injective R (FractionRing O))).toAlgebra
  haveI hRKF : IsScalarTower R K (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R (FractionRing O)) x).symm)
  haveI faithfulRKprime : FaithfulSMul R (FractionRing S) :=
    (faithfulSMul_iff_algebraMap_injective R (FractionRing S)).mpr (by
      rw [IsScalarTower.algebraMap_eq R S (FractionRing S)]
      exact (IsFractionRing.injective S (FractionRing S)).comp hinjRS)
  letI algKK' : Algebra K (FractionRing S) :=
    (IsFractionRing.lift (g := algebraMap R (FractionRing S))
      (FaithfulSMul.algebraMap_injective R (FractionRing S))).toAlgebra
  haveI hRKKprime : IsScalarTower R K (FractionRing S) :=
    IsScalarTower.of_algebraMap_eq (fun x =>
      (IsFractionRing.lift_algebraMap (FaithfulSMul.algebraMap_injective R (FractionRing S)) x).symm)
  haveI faithfulSF : FaithfulSMul S (FractionRing O) :=
    (faithfulSMul_iff_algebraMap_injective S (FractionRing O)).mpr (by
      rw [IsScalarTower.algebraMap_eq S O (FractionRing O)]
      exact (IsFractionRing.injective O (FractionRing O)).comp hinjSO)
  letI algK'F : Algebra (FractionRing S) (FractionRing O) :=
    FractionRing.liftAlgebra S (FractionRing O)
  haveI hSKprimeF : IsScalarTower S (FractionRing S) (FractionRing O) :=
    FractionRing.isScalarTower_liftAlgebra S (FractionRing O)
  haveI hRKprimeF : IsScalarTower R (FractionRing S) (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq (fun r => by
      rw [IsScalarTower.algebraMap_apply R S (FractionRing S) r,
        ← IsScalarTower.algebraMap_apply S (FractionRing S) (FractionRing O),
        ← IsScalarTower.algebraMap_apply R S (FractionRing O)])
  haveI hKKprimeF : IsScalarTower K (FractionRing S) (FractionRing O) :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      have h : (algebraMap (FractionRing S) (FractionRing O)).comp
          (algebraMap K (FractionRing S)) = algebraMap K (FractionRing O) :=
        IsLocalization.ringHom_ext (nonZeroDivisors R) (by
          ext r
          simp only [RingHom.comp_apply]
          rw [← IsScalarTower.algebraMap_apply R K (FractionRing S),
            ← IsScalarTower.algebraMap_apply R (FractionRing S) (FractionRing O),
            ← IsScalarTower.algebraMap_apply R K (FractionRing O)])
      exact (RingHom.congr_fun h x).symm)
  refine ⟨algKF, algKK', algK'F, ?_⟩
  exact ⟨faithfulRF, faithfulRKprime, faithfulSF, hRSKprime, hROF, hSOF, hRSF,
    hRKF, hRKKprime, hSKprimeF, hRKprimeF, hKKprimeF⟩

end P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
