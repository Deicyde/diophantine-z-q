# Results log

- Base: `f2c6dbc7d2696fa5e73370f18931325de5c51845`.
- Captured `check-before.txt` against unchanged sources. The initial build
  found a missing companion artifact in the dependency cache. The retry
  used the matching public, server and private artifacts together.
- Removed 49 commands across the 11 listed WitnessSpec modules.
- Rebuilt all edited modules and the two intervening dependencies with
  serial `lake env lean -j1` invocations. The load and available memory
  checks passed before each invocation.
- Reran all 82 statement checks. The unified diff of `check-before.txt`
  and `check-after.txt` was empty. Both files have SHA-256
  `0511b95954a0d9aa5037ae97358ed60793989a5b7fb28c150a64c06f0925b918`.
- All 74 axiom reports agree with the baseline and cover all 41 theorems.
  The axiom set is limited to `propext`, `Classical.choice`, and `Quot.sound`.
- `git grep` found no `local notation` or other requested local syntax in
  WitnessSpec. No Lean sources outside the 11 intended files were changed.
