import ZInQKernel.Contrib.CloudR2CM.SerreTate.RigidityFinal
import ZInQKernel.Contrib.CloudR2CM.SerreTate.TorsionFieldProof

/-!
# P2: `P2SerreChoice`

Rigidity at each place (`p2InertiaRigidity_proof`) and the choice of `L₁`
(`p2TorsionField_proof`).
-/

set_option autoImplicit false

namespace HDec.CMSerreTate

/-- **P2**: rigidity at each place and the choice of `L₁`. -/
theorem p2SerreChoice_proof : P2SerreChoice :=
  ⟨p2InertiaRigidity_proof, p2TorsionField_proof⟩

end HDec.CMSerreTate
