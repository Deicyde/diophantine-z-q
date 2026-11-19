import ZInQKernel.Contrib.CloudR2CM.SerreTate.RigidityProof
import ZInQKernel.Contrib.CloudR2CM.SerreTate.SerreLemmaTateProof

/-!
# P2, rigidity at one place: `P2InertiaRigidity`

`p2InertiaRigidity_of_serre` applied to the proof of Serre's lemma.
-/

set_option autoImplicit false

namespace HDec.CMSerreTate

/-- **P2, rigidity at one place.** -/
theorem p2InertiaRigidity_proof : P2InertiaRigidity :=
  p2InertiaRigidity_of_serre serreLemmaTate_proof

end HDec.CMSerreTate
