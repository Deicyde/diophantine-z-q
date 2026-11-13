import ZInQKernel.HDecomp.QM.Leaves
import ZInQKernel.HDecomp.Repo.PRArith
import ZInQKernel.Hypotheses.JHeight

/-!
# fs5-nocm: FS5 `FibreComTrivial` (NoCM on the fibre) from NoCM's inputs

Task fs5-nocm (2026-11-13). See `docs/research/fs5-nocm.md`.

* §A (copied verbatim from `scratch/qm-pin/QMPin.lean`, lines 34-94 and 507-619): `QMFamily`,
  `IsFibreOf`, `R1famProps`, `R1fpPropsPin`, `R1univProps`, `R1fpPropsU`, `SameTripleMor`,
  `transfer_pointwise_mor`, `phi_part`, `MobiusGlue`, `sameTripleMor_of_mobius`,
  `pointwise_of_witness_mor`, `cm_objects_of_R1R2fp`.
* §B FS5 as in `scratch/g0-fibresimple/FibreSimple.lean` (verbatim) and with qm-pin's full repair
  of `R1fpProps` (text of `scratch/qm-pin/QM-Leaves-full.patch`).
* §C the named Props NoCM still needs; §D the arithmetic; §E the proof.
No `sorry`, no `axiom`.
-/

noncomputable section

