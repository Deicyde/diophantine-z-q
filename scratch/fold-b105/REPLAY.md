# fold-b105: replaying the three folds on a later head

The Contrib proof files are separate commits (merges of semistab-assembly and pb-p1, plus the hygiene commit
with the R11 docstring fix). The folds themselves are produced by scripts. From the repository root, on a head
that has the Contrib files (ChevalleyFree.lean, SemistablePrintedReadings.lean, PanBergerFontaine.lean) and
still carries `chevalleyPerfect`, `bostLowerBoundAn`/`gaudronRemondThm14An` and `panPrintedP`/`bergerPrintedVT`:

    python3 scratch/fold-b105/gen_chev_bypass.py            # fold 1: TailZ<j>, -chevalleyPerfect
    # build + checks (bash scratch/fold-b105/run_checks.sh 1 <base dump>), commit
    python3 scripts/one_proof/autofold.py scratch/fold-b105/autofold-semistab.json   # fold 2
    # build + checks, commit
    python3 scratch/fold-b105/gen_pbp1_bypass.py            # fold 3
    # move panPrintedP's row from docs/one-proof/reviews.tsv to reviews-retired.tsv (render_open's row check),
    # then build + checks, commit

Each script takes Main.lean's current top theorem and follows its chain. Let-steps and nested conversion
composites are allowed. Each script stops at the first bundle that lacks the removed field(s), so further
autofolds on top are composed through. Use `--dry-run` to print the module without writing anything.

Replay test, text only (VERIFIED 11-17 06:37, temporary worktree at d67ea55f, since removed):
1. A fake autofold removed `neronOggShafarevichSep` with a proof that uses `{t}`.
2. The three scripts then ran in order and produced TailZ76/77/78.
3. The walks were one step longer, with the same stop bundle `OpenResearchLeaves36EBCF`, the same readers, and the
   fake proof inlined in the composite.
4. Counts went 4/26 on 30 -> 4/25 on 29 (fake) -> 4/25 on 29.

`run_checks.sh K PREV` runs, one Lean process at a time:
- DumpCompact, with the hash comparison against /tmp/fb105/PREV;
- FoldCheck (closure; edit its `checked` list for the fold);
- OpenStatements;
- render_open, DischargesTest, render_open again, and `--check`;
- frontier_crosswalk and its `--check`;
- the autoform check.

The base dump for fold 1 was taken against the base oleans. Run `lean` with LEAN_PATH pointed at a base build
tree (see log step 4).
