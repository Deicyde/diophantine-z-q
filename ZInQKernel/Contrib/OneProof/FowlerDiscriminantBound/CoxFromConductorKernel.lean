import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ConductorProduct
import ZInQKernel.Contrib.OneProof.FowlerDiscriminantBound.ConductorScalarResidues

/-! The scalar residue group has the totient cardinality in the conductor product. -/

namespace HDec.CMBranch.FowlerArithmetic

open TauCeti.GlobalNumberFields

variable {K : Type*} [Field K] [NumberField K]

/-- Only the ray-class kernel identification remains in the conductor product formula. -/
theorem coxConductorProduct_of_conductor_kernel
    (O : NumberFieldOrder K) (hK : Module.finrank ℚ K = 2)
    (hker : (conductorUnitsToPic O).ker =
      (maximalUnitsModConductor O).range ⊔ orderResidueUnitSubgroup O) :
    CoxConductorProduct O :=
  coxConductorProduct_of_residue_identifications O hK hker
    (card_orderResidueUnitSubgroup_eq_totient O hK)

end HDec.CMBranch.FowlerArithmetic
