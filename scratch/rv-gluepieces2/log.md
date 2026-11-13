# rv-gluepieces2 results log

Target: the 27 fields of `HSyn.GluePieces2` in scratch/g0-assemble/G0Assemble.lean (L41938-41998).

- VERIFIED (cmp/diff): scratch/g0-assemble/Leaves.lean differs from scratch/h-decomposition/Leaves.lean
  (current, post pin-apply) exactly by pin-apply's patch: `R1famProps`, `R1univProps`, `QMFamily`,
  `IsFibreOf` and namespace `Pin` are absent from G0Assemble.lean; its `R1fpProps` is the
  pre-repair 4-clause version (no fam/univ clauses).
