# milne-compile

**Result: `milneIsogenyQuasiInverse` proved outright, no new leaf (-1 field).** Draft fork PR #23's 16-module
source (kernel group scheme, finite-Hopf annihilator and fpqc power descent vendored from openai/math 4eaee875
under Apache-2.0; new ring/scheme flatness and assembly) compiles on Lean 4.35.0 / Mathlib v4.35.0 after two
technical fixes: a shadowed `this` in `Flatness.flat_of_kernelPair`, and a local instance
`Kernel.kernelGroup` in `Main`. No statement changed; only files under `ZInQKernel/Contrib/OneProof/Milne*`.

* `ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof : AvSplit.MilneIsogenyQuasiInverse`, axioms
  `[propext, Classical.choice, Quot.sound]`.
* `#discharges`: `DISCHARGES [OpenAddedLeaves17.milneIsogenyQuasiInverse]`, still assumes `[]`
  (`scratch/milne-compile/discharges-output.txt`); field type equals the theorem's by `rfl` (`CheckField.lean`).
* `scratch/milne-compile/autofold.json`; its `--dry-run` module compiles (`sixContactMin_of_open36`, standard
  axioms); strict 34/11 on 45 -> 33/11 on 44.

Remains: the integrator's fold (autofold, build, hash comparison, OPEN.md regeneration) and the PR #23 update.
Report: `docs/research/milne-compile.md`.
