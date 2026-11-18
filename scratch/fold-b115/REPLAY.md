# fold-b115: replaying the folds on a later head

The merged branches are separate commits (ss-faltings merge 86231f4c; pb-dimform merge 785db9ac; htmult-model's five
own commits cherry-picked). Replay order, from the repository root of a head that has them. After each step build
`ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges` plus the touched modules, then
`bash scratch/fold-b115/run_checks.sh K PREV` (dumps in /tmp/fb115; edit the `checked` list and the field-check
bundle names in `scratch/fold-b115/FoldCheck.lean` if the bundle numbers moved), then commit.

1. ss-faltings (bypass; no autofold spec: nothing is discharged outright):

       python3 scratch/fold-b115/fold_ssf.py [TOP_MODULE R0 OLD_TOP NEWR NEW_TOP TEXTBOOK ADDED]

   Defaults: `ZInQKernel.OneProof.H.TailZ83 OpenResearchLeaves57 sixContactMin_of_open76 OpenResearchLeaves58
   sixContactMin_of_open77 OpenTextbookLeaves18 OpenAddedLeaves27`. It runs ss-faltings' `gen/gen_bypass.py` with
   these arguments, writes `ZInQKernel/OneProof/H/TailZ<next>.lean`, `git mv`s the generated chain
   `Contrib/OneProof/SSFChain.lean` to `OneProof/H/SSFChain.lean`, edits Main (import, bundle, top, docstring
   paragraph) and replaces the `sga7_IX_Cor3_3_Def34` kinds row. Use names of the form `OpenResearchLeaves<n>` /
   `sixContactMin_of_open<n>`: autofold (and so `scratch/lane74/gate.sh`) cannot parse `sixContactMin_of_open77sf`.
   If the top is no longer `sixContactMin_of_open76`, first regenerate SSFChain on it (ss-faltings report section 3:
   `scratch/ss-faltings/TaintS.lean` import and `topName`, then `gen/gen_chain.py OUT TOPMOD TOP`), writing it
   directly to `ZInQKernel/OneProof/H/SSFChain.lean` and fixing the import line that fold_ssf.py rewrites.
2. Tau Ceti pin lines: the commit d4fb006a is a plain three-line source edit (cherry-pick it). Expect a full rebuild of
   the OneProof chain (about 20 min on this host).
3. pb-dimform + htmult-model (no Lean fold):

       python3 scratch/fold-b115/row_edits_q29.py         # kinds.tsv rows panPrintedF, bergerSurveyF
       python3 scratch/fold-b115/field_docs_q29.py [TailZ files] [--allcontrib]   # field docstrings (default TailZ83, TailZ84)

   then `python3 scripts/one_proof/render_open.py`. `--allcontrib` appends HTModel to AllContrib: only on a head that
   has wip/contrib-clashes; without it the import fails (log.md fold 3 item 5).
