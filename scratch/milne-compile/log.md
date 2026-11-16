# milne-compile results log

Base: origin/proof/milne-quasiinverse-20261115 0eab413d, merged origin/main (2880fef1e) -> 20da149e8.
Build tree: reflink copy of ~/dzq-wt/pic-fix/.lake/build (be79cb5b9; differs from this tree only in ZInQKernel/Contrib/).

## Compile log
- VERIFIED (compiled, `lake build`): 9 vendor modules (DualAlgebra ... FormalGeometry/Completion/Finite/GroupAnnihilator),
  `MilneQuasiInverse.GroupAnnihilator`, `Kernel`, `Descent`, `RingFlatness` compile with NO change (only linter /
  module-system warnings).
- VERIFIED: `Flatness.lean` failed once: line 125 `Function expected at this ... IsAffine X` (an anonymous
  `have : IsAffine X` shadowed the `wlog` hypothesis `this`). Fix: name it `hXaff`. Then compiles.
- VERIFIED: `Main.lean` failed: `failed to synthesize MonObj (Kernel.kernelGrp f.hom).X` and
  `IsCommMonObj (Kernel.kernelGrp f.hom).X` (reducible `kernelGrp` unfolds to `kernelObject f.hom`, whose group
  structure `Kernel.kernelGroup` is only a local instance). Fix: `attribute [local instance] Kernel.kernelGroup`
  in Main. Then `ZInQKernel.Contrib.OneProof.MilneIsogenyQuasiInverse` builds.
- VERIFIED: `#print axioms ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof` = [propext, Classical.choice, Quot.sound].
- VERIFIED: scratch/milne-compile/Check.lean, `#discharges`:
  `DISCHARGES [OpenAddedLeaves17.milneIsogenyQuasiInverse] by ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof`,
  `still assumes: []`, axioms standard. Output: discharges-output.txt.
- VERIFIED: scratch/milne-compile/CheckField.lean: for `b : HDec.HSyn.OpenAddedLeaves17`,
  `b.milneIsogenyQuasiInverse = milneIsogenyQuasiInverse_proof := rfl` compiles (field type = theorem type).
- VERIFIED: autofold.json; `autofold.py --dry-run`: strict 34/11 on 45 -> 33/11 on 44, strictest 34/11 -> 33/11;
  dry-run module (AutofoldDryRun.lean = output minus line 1) compiles, `sixContactMin_of_open36` standard axioms.
- No new leaf. No statement changed. Only files under ZInQKernel/Contrib/OneProof/Milne* differ from origin/main.
