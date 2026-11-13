# leaf-adopt3 results log

## Setup
- 01:16 merged origin/wip/g0-split, wip/h5-neron, wip/t10-etale (scratch + docs only; their .fleet notes dropped).
- Infrastructure: `scratch/leaf-adopt3/olean/HDPrefix.lean` = Leaves.lean lines 1-21087 (everything before HSyn),
  compiled to an olean so the tail can be iterated quickly (`import HDPrefix`, LEAN_PATH=olean dir).
- 01:23 prefix olean built (4m10s, 0 errors).
- 01:28 Tail (GlueSSBCSec + HSyn §0-§2 + bundles + adapted g0-split part + trailer) compiled against the
  prefix olean: exit 0, 0 errors, 170 s. `HSyn.sixContactMin_of_leaves`, `glueOutputs_of_leaves`: standard
  axioms only. G0 now takes `(r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces)`; R18/R22 come from
  r.r18/r.r22 + glue piece HeightCopiesAgree (`r18Concrete_of`, `r22Concrete_of`, proved first try).
- Leaves.lean assembled (prefix + parts) and committed: no `sorry`.
- 01:4x t-different fragment: tail compile exit 0, 0 errors (194 s).
- 01:38 tail with fragments t-different, t-skolem-kw, t30-adelic (T30 + copied kernel SqrtChar/SqrtLocal/Disj), t10-etale,
  pi0-x6, hodge-lattice, h5-neron (prepared by read-only subagents from the task files, BRIEF in fold/): exit 0,
  0 errors, no sorry, 137 `#print axioms` lines (363 s). Fragments compiled on the first attempt.
- Repairs agent: apply_repairs.py (12 docstring replacements, tested on copies: code byte-identical after stripping
  comments) and direct edits of h-decomposition.md (P1, P2, P4, P6 of rv-leaves48; fact-check items 1, 3, 5, 8, 14, 18).
  It reports that factcheck-w34b does not itself mention rows C2/E1/WP3/WP5/WP13 (see repairs_report.md).
- 01:5x first tail with all ten fragments (+ x1-belyi, e1-sub, c9-rhof) and the bundle edits: one error,
  e1-sub `bcPt.map_one'`: `rfl` after `rw` had no goal in Leaves.lean's context (dropped, commented).
- 02:0x tail with all fragments, new bundles (t10 concrete; t13, t19, t22a/b, t30 removed; t17 → KroneckerWeberCyclic;
  t18 → ChebotarevExists; new x1 (T36-T40), t41 (N1)), GluePieces.additivity → productModelHeight, derived
  theorems (65_derived), hodge-lattice bridge: exit 0, 0 errors, no sorry, all `#print axioms` standard (380 s).
- 02:1x FULL CHECK: `lake env lean scratch/h-decomposition/Leaves.lean` (33 921 lines, assembled by
  `assemble.py full` = base prefix + parts + header_edits.py + apply_repairs.py): exit 0 in 574 s, 0 errors,
  no `declaration uses 'sorry'`, 174 `#print axioms` lines, all `[propext, Classical.choice, Quot.sound]`
  (incl. HSyn.sixContactMin_of_leaves); 2 `opaque` (R01b, R17), no `axiom`. Output: compile_full.txt.
- Statement diff (stmt_diff.py, base 883c4ddf vs new, comments stripped, 1683 base decls): changed only
  HSyn.TextbookLeaves, HSyn.glueOutputs_of_leaves, HSyn.sixContactMin_of_leaves; removed only
  HSyn.T10_TateDuality (opaque). ResearchLeaves unchanged.
- Fold diff (fold_diff.py, task files vs new Leaves.lean): every copied declaration identical except
  TSkolemKW.C10.{brauerNesbittChar0', c10_of_chebotarev} (now over GlueC10's identical originals),
  T10Etale.T10_groupIso_of_linIso (now concludes ZInQ.LeafPush2.T10_groupIso, the identical original),
  E1Sub.bcPt (an `rfl` dropped).
