# fold-b112: replaying the folds on a later head

The Contrib proof files are separate commits (the five merges, and the fold-b112 Contrib commit
`ZInQKernel/Contrib/OneProof/GaudronRemondSection9SS.lean`). The folds are produced by scripts, in this order, from the
repository root of a head that has those Contrib files. Each step: build `ZInQKernel.OneProof.Main
ZInQKernel.OneProof.Discharges` plus the new TailZ module, then `bash scratch/fold-b112/run_checks.sh K PREV` (edit the
`checked` list and the field-check bundle names in `scratch/fold-b112/FoldCheck.lean` for the fold), then commit.

1. bost-gr9 (weaker-leaf bypass; needs `bostLowerBoundAnSS` in Main's research bundle):

       python3 scratch/fold-b112/gen_gr9_fold.py closure        # writes GR9Closure.lean for Main's current top
       lake env lean scratch/fold-b112/GR9Closure.lean          # ~2.5 min, writes gr9-closure.tsv
       python3 scratch/fold-b112/gen_gr9_fold.py --dry-run      # optional: count line + module
       python3 scratch/fold-b112/gen_gr9_fold.py                # TailZ<j>, Main, kinds.tsv, claims.tsv
       python3 scratch/fold-b112/row_edits_64b.py               # inbox 64b (bergerSurveyF source), same commit

   The generator copies every declaration reachable from Main's top theorem whose type mentions a bundle carrying the
   Bost field (any form), so further autofolds on top are copied through (the closure grows by their bundles and
   conversions); the top research bundle becomes the next `OpenResearchLeaves<n>`. It refuses a stale closure file.
2. sz-raynaud: `python3 scripts/one_proof/autofold.py scratch/fold-b112/autofold-sz.json`
3. (row edits: done in step 1)
4a. y3-route-a: `python3 scripts/one_proof/autofold.py scratch/fold-b112/autofold-y3.json`
4b. carirr-refold: `python3 scripts/one_proof/autofold.py scratch/fold-b112/autofold-car.json`; then move the
    `carayolThmAIrr` row of docs/one-proof/reviews.tsv to reviews-retired.tsv (render_open's row check) and rerun
    render_open.
5. r3prime-etale + r3prime-bc: no Lean fold (no field discharged); `python3 scratch/fold-b112/r3prime_flags.py` edits
   the three kinds.tsv flags; rerun render_open.

The autofold specs are the branches' own specs, unchanged (copied so that the replay does not depend on the branches'
scratch directories). The hash dumps (DumpCompact, ~1.7 MB each) are in /tmp/fb112 and are not committed; the
comparisons are `cmp_fold<K>.txt`.
