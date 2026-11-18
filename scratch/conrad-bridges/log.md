# conrad-bridges results

- VERIFIED (git): base `15c9e93d3` (the joint fold, `OpenAddedLeaves28.conradAppB`).
- VERIFIED (Lean): `Original.lean` copies the three target Props and their immediate local predicates; three `Iff.rfl` checks match the original types.
- VERIFIED (source): manuscript `sec:height`, lines 755–767 and bibliography lines 11046–11049; repository audit A011, lines 102–108, confirms the exact author version and application with local base `ℚ₅`, finite coefficient field, and arithmetic reciprocity.
- VERIFIED (source): supplied App. B page read gives the near-one product formula (p. 33; one factor over `ℚ_p)) and Prop. B.3's weight label. No independent PDF read in this worktree.
- VERIFIED (Lean): `ConradBridges.lean` compiled without warnings at its contribution module path. It defines the full-group tensor splitting, the near-one formula, the restriction to the finite Galois coefficient field and the identity line statement. The exact old conclusion is `conradAppB_of_concrete : ConradAppBConcrete → ConradAppB`.
- VERIFIED (autofold generator, dry run): `OpenAddedLeaves29` replaces only `conradAppB` with `conradAppBConcrete`. H strict LEAF/GLUE on N: 5/24 on 29 → 5/24 on 29. Under the task's refereed-source rule the author preprint stays GLUE. The count with a preprint exception would be 6/23 on 29.
- VERIFIED (build cache inventory): the copied artifacts lack `TailZ87` and the pinned `Main`; a source-matched cache scan left 330 project modules to compile, including 294 under `CloudR2Poincare`. Generator output is not a Lean run of the top.
- VERIFIED (Lean, final): `Original.lean` also compiles with the copied `unitsQp`, `IsArtinLift` and `charRep`. All seven `#print axioms` checks in `Axioms.lean` give only propext, Classical.choice and Quot.sound; see `axioms-out.txt`.
