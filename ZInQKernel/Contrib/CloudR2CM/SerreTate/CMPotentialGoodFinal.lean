import ZInQKernel.Contrib.CloudR2CM.SerreTate.AssemblyProof
import ZInQKernel.Contrib.CloudR2CM.SerreTate.CMFieldOfDefinitionProof
import ZInQKernel.Contrib.CloudR2CM.SerreTate.P1.TameGeneratorInputBinding
import ZInQKernel.Contrib.CloudR2CM.SerreTate.SerreChoiceProof
import ZInQKernel.Contrib.CloudR2CM.SerreTate.P3GoodReductionProof
import ZInQKernel.Contrib.CloudR2CM.SerreTate.P4.ProperModelProof

/-!
# `CMPotentialGood` from the existence of Néron models over Dedekind schemes

`HDec.CMBranch.CMPotentialGood`, with `ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind` as the
only hypothesis: the assembly `cmPotentialGoodAssembly_proof` applied to the proved route statements

* P0 `cmFieldOfDefinition_proof` (the CM field of definition),
* P1 `P1.p1FiniteInertia_proved` (finite inertia image on the Tate module),
* P2 `p2SerreChoice_proof` (Serre's rigidity at each place and the choice of `L₁`),
* P3 `p3GoodReduction_proved` (good reduction at each finite place, from the converse of the
  criterion of Néron–Ogg–Shafarevich),
* P4 `P4.p4ProperModel_proved` (the proper global model, from good reduction at every finite place and
  the existence of Néron models).
-/

set_option autoImplicit false

namespace HDec.CMSerreTate

/-- **`CMPotentialGood`**, with the existence of Néron models over a Dedekind scheme as the only
hypothesis. -/
theorem cmPotentialGood_of_neronSchemeExtensionDedekind
    (hN : _root_.ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind) :
    _root_.HDec.CMBranch.CMPotentialGood :=
  cmPotentialGoodAssembly_proof cmFieldOfDefinition_proof
    _root_.HDec.CMSerreTate.P1.p1FiniteInertia_proved p2SerreChoice_proof p3GoodReduction_proved
    _root_.HDec.CMSerreTate.P4.p4ProperModel_proved hN

end HDec.CMSerreTate
