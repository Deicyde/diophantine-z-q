# Results log

- Base: `c653a7426f795b39762764fa31999a53c9e5922c`. The initial notation scan found only `ExactGenus.lean:21`.
- `Check.lean` imports `ExactGenus` and checks all four declarations, with notation disabled and implicit arguments shown.
- The local build cache lacked the stage modules. Verification uses the dependency cache from the matching base revision with a separate output directory for the rebuilt module.
- Compiled the unchanged `ExactGenus.lean` and saved the baseline in `scratch/rc-stages-ln/check-before.txt` before editing the source.
- Removed the `H` notation and inlined `ringClassField (conductorOrder K c)` at its uses. Recompiled the changed module and saved `scratch/rc-stages-ln/check-after.txt` with the same check file. Both compiles had the same existing linter warnings.
- Ran each Lean command serially with `-j1`, checking load and available memory before each run.
- `diff` was empty. Both outputs have SHA-256 `1c8d5d6b159504647d29eb84f6c64de840b24b56473f06adde2a9645c21f44ba`.
- `#print axioms` reported exactly `[propext, Classical.choice, Quot.sound]` for `twistEmb_mem_eigenLattice`, `uniform_kills_native`, `exact_twist_of_genus`, and `exact_twist_of_genusPoint`.
- `git grep` found no remaining `local notation` and no other local syntax declarations of the requested kinds under `ZInQKernel/Contrib/OneProof/RC/Stages/`.
