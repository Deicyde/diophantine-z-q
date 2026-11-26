import ZInQKernel.Contrib.OneProof.EllAdic.FiniteAbDictionary
import ZInQKernel.Contrib.OneProof.EllAdic.ConstantComparisonRebaseV1
import ZInQKernel.Contrib.OneProof.EllAdic.ExtOneRebaseTransportV1
import ZInQKernel.Contrib.OneProof.EllAdic.SmallEtaleResidueHOneForwardV1

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped RC53.EllAdic.FiniteAbDictionary

namespace RC53.EllAdic

universe u

local instance geomFiniteEtaleEquivalence {S T : Scheme.{u}} (σ : S ≅ T) :
    (etaleAbRebasePullback σ).IsEquivalence :=
  inferInstanceAs (etaleAbRebaseEquivalence σ).functor.IsEquivalence

local instance geomFiniteProEtEquivalence {S T : Scheme.{u}} (σ : S ≅ T) :
    (proEtAbRebasePullback σ).IsEquivalence :=
  inferInstanceAs (proEtAbRebaseEquivalence σ).functor.IsEquivalence

local instance geomFiniteEtaleAdditive {S T : Scheme.{u}} (σ : S ≅ T) :
    (etaleAbRebasePullback σ).Additive :=
  Functor.additive_of_preserves_binary_products _

local instance geomFiniteProEtAdditive {S T : Scheme.{u}} (σ : S ≅ T) :
    (proEtAbRebasePullback σ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The same pullback on the actual pro-étale residue coefficients. -/
noncomputable def proEtResidueHOne_rebase {S T : Scheme.{u}} (σ : S ≅ T) (p n : ℕ) :
    ((liftedFiniteResidueProEtSheafTower T p).obj (op n)).H 1 →+
      ((liftedFiniteResidueProEtSheafTower S p).obj (op n)).H 1 :=
  let z : Ab.{u+1} := FiniteAbDictionary.zCoeff
  extOneTransport (proEtAbRebasePullback σ) ((proEtConstantRebaseIso σ).hom.app z)
    (liftedFiniteResidueProEtRebaseIso σ p n).hom

/-- The same pullback on the literal finite constant étale coefficients. -/
noncomputable def etaleResidueHOne_rebase {S T : Scheme.{u}} (σ : S ≅ T) (p n : ℕ) :
    (etaleConstantResidue T p n).H 1 →+ (etaleConstantResidue S p n).H 1 :=
  let z : Ab.{u+1} := FiniteAbDictionary.zCoeff
  extOneTransport (etaleAbRebasePullback σ) ((etaleConstantRebaseIso σ).hom.app z)
    ((etaleConstantRebaseIso σ).inv.app (liftedResidueCoefficient.{u} p n))

end RC53.EllAdic
