/-
Multiplication-etale construction: LocalPushoutCriterion.
The mathematical declarations below are part of the checked H-101 contribution.
-/
import ZInQKernel.Contrib.MulEtale.Direct.Global.BaseChangeCriterion
import ZInQKernel.Contrib.MulEtale.Direct.Global.ResidueAlgebraCoherence

noncomputable section
open scoped TensorProduct
namespace H101DirectGlobalDetection

section LocalPushouts
variable (R S T R' S' T' : Type*)
  [CommRing R] [CommRing S] [CommRing T]
  [CommRing R'] [CommRing S'] [CommRing T'] [IsLocalRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  [Algebra.EssFiniteType R S] [Algebra.EssFiniteType R T]
  [Algebra.FormallySmooth R S] [Algebra.FormallySmooth R T]
  [Algebra R R'] [Algebra R' S'] [Algebra S S'] [Algebra R S']
  [IsScalarTower R S S'] [IsScalarTower R R' S']
  [Algebra R' T'] [Algebra T T'] [Algebra R T']
  [IsScalarTower R T T'] [IsScalarTower R R' T']
  [Algebra S' T'] [Algebra S T']
  [IsScalarTower R' S' T'] [IsScalarTower S S' T'] [IsScalarTower S T T']
  [Algebra.IsPushout R R' S S'] [Algebra.IsPushout R R' T T']

variable [Algebra T' (IsLocalRing.ResidueField T)] [Algebra S' (IsLocalRing.ResidueField T)] [Algebra R' (IsLocalRing.ResidueField T)]
  [Algebra S (IsLocalRing.ResidueField T)] [Algebra R (IsLocalRing.ResidueField T)]
  [IsScalarTower S T (IsLocalRing.ResidueField T)] [IsScalarTower R T (IsLocalRing.ResidueField T)] [IsScalarTower R S (IsLocalRing.ResidueField T)]
  [IsScalarTower S' T' (IsLocalRing.ResidueField T)] [IsScalarTower R' T' (IsLocalRing.ResidueField T)] [IsScalarTower R' S' (IsLocalRing.ResidueField T)]
  [IsScalarTower T T' (IsLocalRing.ResidueField T)] [IsScalarTower S S' (IsLocalRing.ResidueField T)]

include R R' in
/-- Smooth structural stalks with a formally-etale base-changed stalk map
are formally etale along the investigated map. This is a proved SOURCE
callchain, not a claim that the actual scheme-fibre scalars/maps are joined. -/
theorem formallyEtale_of_formallyEtale_baseChange
    [Algebra.FormallyEtale S' T'] : Algebra.FormallyEtale S T := by
  have h : Function.Bijective
      (H101DirectFieldRoute.residueCotangentMap R S T (IsLocalRing.ResidueField T)) :=
    residueCotangentMap_bijective_of_formallyEtale_pushout R S T R' S' T' (IsLocalRing.ResidueField T)
  have hScoef : (inferInstance : Algebra S (IsLocalRing.ResidueField T)) =
      (IsLocalRing.ResidueField.algebra T : Algebra S (IsLocalRing.ResidueField T)) :=
    ResidueAlgebraCoherence.algebra_eq_canonical S T
      (inferInstance : Algebra S (IsLocalRing.ResidueField T)) inferInstance
  have hRcoef : (inferInstance : Algebra R (IsLocalRing.ResidueField T)) =
      (IsLocalRing.ResidueField.algebra T : Algebra R (IsLocalRing.ResidueField T)) :=
    ResidueAlgebraCoherence.algebra_eq_canonical R T
      (inferInstance : Algebra R (IsLocalRing.ResidueField T)) inferInstance
  cases hScoef
  cases hRcoef
  exact formallyEtale_of_actual_residueCotangentMap_bijective R S T h

end LocalPushouts
end H101DirectGlobalDetection
