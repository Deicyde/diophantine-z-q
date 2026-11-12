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
