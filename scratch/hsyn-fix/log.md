# hsyn-fix results log

- 23:39 `lake build ZInQKernel.Hypotheses.JHeight`: success (9066 jobs).
- 23:39 note: rv-hsyn repairs 1-3, 5-10 applied with its exact texts (repair 4 rewritten for the new sorry list).
- Leaves.lean: A6 from rv-a6-route §10 (with hypothesis `QuatUnipotentTrivial`); D4 from
  glue-I6-rest Conductor.lean (section Proof); D3 `PkgI6.sq_principalUnits` proved from
  `HSyn.sq_principalUnits_proved`; glue-I3-linalg C2.lean §0 (namespace GlueI3) and §5
  (C2, E1, with hypothesis `SemisimpleBaseChange`).
- 23:41-23:44 `lake env lean scratch/h-decomposition/Leaves.lean`: exit 0, 3m08s, one
  "declaration uses sorry" (glueOutputs_of_leaves). 28 `#print axioms`: all
  [propext, Classical.choice, Quot.sound] except `HSyn.sixContactMin_of_leaves` (sorryAx). 0 `axiom`, 19 `opaque`.
- 23:45-23:47 compile after rv-leaves-a/b repairs (Pazuki `+3` in `PazukiOutput` and
  `pazuki_numerics`; bundle uses `BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`): exit 0, no errors.
- 23:47-23:49 final compile with 17 more `#print axioms`: exit 0, 1m28s, no errors; one
  "declaration uses sorry" (`HSyn.glueOutputs_of_leaves`); 45 `#print axioms`, 44 give
  [propext, Classical.choice, Quot.sound], `HSyn.sixContactMin_of_leaves` adds sorryAx.
  `grep -c '^opaque'` = 19, `grep -c '^axiom'` = 0. Counts unchanged: 35 of 54 leaves, 39 Props.
- Named glue Props taken as hypotheses: `PkgI2.QuatUnipotentTrivial`, `GlueI3.SemisimpleBaseChange`.
- §0 word count 1389 -> 1640 (+18%).
