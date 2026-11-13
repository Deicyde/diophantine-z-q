
/-! ## fs1-descend integration tail (appended by `check_integration.sh`) -/

namespace G0FibreSimple

open HSyn HSyn.G0Split

/-- FS1b′ is proved (scratch/fs1-descend). -/
theorem finiteDescends_proof : FiniteDescends := FS1Descend.finiteDescends

/-- **`FibreSimple` from the leaf bundle, the textbook leaves `MulIsogeny`, `RigidityHom` and the
single remaining glue piece FS5 `FibreComTrivial`** (FS1b′ is now proved). -/
theorem fibreSimple_of_leaves_fs5 (t : HSyn.TextbookLeaves) (hMul : MulIsogeny)
    (hRig : RigidityHom) (hCom : FibreComTrivial) : FibreSimple :=
  fibreSimple_of_leaves t hMul hRig ⟨finiteDescends_proof, hCom⟩

end G0FibreSimple

#print axioms G0FibreSimple.finiteDescends_proof
#print axioms G0FibreSimple.fibreSimple_of_leaves_fs5
