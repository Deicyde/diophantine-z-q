# kf-glue results log

Base: wip/integrate-w38b (f90cf864) + merges of origin/wip/kernel-field, origin/wip/mul-rigidity.

## Step 1. EndTransport (medium)
- `scratch/kf-glue/KfGlue.lean` = `assemble.sh` output: KernelField.lean (verbatim, one porting fix in a
  proof term: `hR1.2.2.2` -> `hR1.2.2.2.1`, since R1fpProps has 6 clauses on this base) + MulRigidity.lean
  lines 3-182 (verbatim) + `scratch/kf-glue/New.lean`.
- `theorem G0ModField.KernelField.endTransport : EndTransport` (no hypotheses) =
  `endTransport_of (endTransportBC_of_rigidity rigidityHom)`.
- `kernelFieldExists_of_five`: KernelFieldExists from HomFreeFinite, NOS, Raynaud, TorsionStructure,
  QMDichotomyYu, FS5, ConjIsogMaps.
- VERIFIED (compiled, `lake env lean`, rc=0, build1.txt): both axioms [propext, Classical.choice, Quot.sound].
