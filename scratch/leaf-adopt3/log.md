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
