# pi0-prune results log (base 43513d87)

## Scope (VERIFIED, compiled probes)
- `Scope.lean` → Scope_out.txt: tainted structures (carry `R1R2fpRep`): ResearchLeaves3, OpenResearchLeaves2/5/7/8/9;
  57 live constants mention them or `R1R2fpRep` in their type.
- `Reach.lean` → Reach_out.txt: live readers of the projections `OpenAddedLeaves12..17.{deligneComponentsX6PrintedAb,
  geomConnOfAlgClosure}`: 23 constants (x6Rows_of_open14 … sixContactMin_of_open29, the addedLeaves conversions).
- `Copy.lean` → Copy_out.txt: the copy set = tainted-type ∪ readers ∪ everything above them in the closure:
  80 constants (incl. frozenTarget) + 6 structures. Line ranges at base 43513d87.

## Build
- Generator scratch/pi0-prune/tools/gen.py (+ cfg_*.py, common.py): copies declarations by line range keeping the
  source file's namespace/section/open skeleton; renames (suffix W; OpenAddedLeaves12..17 → …P; R1R2fpRep → R1R2fpRepW).
- Pi0Prune/Base.lean: R1R2fpRepW, R1R2fpRepW_of_rep, R1R2fp_of_repW, producers (CoarseX6OfFineW, CanonicalCoarseX6W,
  GeomConnX6W, geomConnX6W_of_gr, r1r2fpRep_of_printedW, r1r2_of_publishedW, x6Rows_of_leavesW) and copied
  destructurers/consumers. COMPILED (lake env lean, 8 s) after 3 pattern fixes (one conjunct fewer in r1rec_of_rep,
  r5fp_of_rep, pairsLift_of_rep).
