
/-! # kf-glue, part 1: `EndTransport` (scratch/kernel-field/New.lean, statement unchanged)

`EndTransport` is defined above (verbatim from scratch/kernel-field). kernel-field proved
`endTransport_of : EndTransportBC → EndTransport` and
`endTransportBC_of_rigidity : RigidityHom → EndTransportBC`; mul-rigidity proved `RigidityHom`
from Mathlib (`MulRigidity.isMonHom_of_geometricallyIntegral`). -/

section KfGlueEndTransport

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **`RigidityHom` holds** (mul-rigidity's proof, verbatim apart from the name). -/
theorem G0FibreSimple.rigidityHom : G0FibreSimple.RigidityHom := fun _ _ A B h h0 =>
  MulRigidity.isMonHom_of_geometricallyIntegral A.X B.X h h0

/-- **`EndTransport` is a theorem** (no hypotheses). -/
theorem G0ModField.KernelField.endTransport : G0ModField.KernelField.EndTransport :=
  G0ModField.KernelField.endTransport_of
    (G0ModField.KernelField.endTransportBC_of_rigidity G0FibreSimple.rigidityHom)

/-- `KernelFieldExists` with `RigidityHom` discharged: five leaves and two glue Props. -/
theorem G0ModField.KernelField.kernelFieldExists_of_five (hHFF : PkgI3.HomFreeFinite)
    (hNOS : PkgI2.NeronOggShafarevich.{0}) (hRay : PkgI2.RaynaudCriterion.{0})
    (hTors : PkgI2.TorsionStructure.{0}) (t27 : PkgI3.QMDichotomyYu)
    (h5 : G0FibreSimple.FibreComTrivial) (hG : G0ModField.KernelField.ConjIsogMaps) :
    G0ModField.KernelFieldExists :=
  G0ModField.KernelField.kernelFieldExists_of_rigidity hHFF hNOS hRay hTors t27
    G0FibreSimple.rigidityHom h5 hG

end KfGlueEndTransport

#print axioms G0ModField.KernelField.endTransport
#print axioms G0ModField.KernelField.kernelFieldExists_of_five
