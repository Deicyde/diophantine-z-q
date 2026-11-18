rc-o12-stage-val: the stage data and the stage valuation for (O.12), from rc-o12-theta's remaining list (base: rc/thm53-proof-20261117 at 40d619ca811e6d8e760c49ac7e273cf5be8b2272, with wip/rc-pm merged in).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", then approved the project's hosts taking Theorem 5.3's appendices. The host task rc-o12-theta left three related inputs (docs/research/rc-o12-theta.md, "Remaining hypotheses"): the identification of the same valid stage, good domain, budget, depth, admissibility and elliptic coefficients across the Odd and theta data (tex 9450-9455, 9471-9489, 9578-9584, 9699-9704); the actual P_M weights and chosen integral lifts (tex 8476-8494, 8600-8621, 9059-9082), which the host task rc-pm has now constructed (wip/rc-pm: P_M(z) = λ_M(L·π_ℓ₀(z)) on the Eichler order's ideal classes; RC/PM/ and RC/AppF/Stage.lean's ThetaStage); and the valuation representative and off-filter support, StageValuation in RC/O12Theta/Inputs.lean (tex 2074-2086, 2522-2538, 9101-9405, 9675-9680, 9694-9704). The root folded rc-o12-local, rc-o12-eisenstein, rc-o12-theta and rc-theta-coeff into this base at e89673d3a (their reports are in docs/research/). The lead approved this follow-up. Do not overlap the sibling tasks: rc-stage-map (RC/StageMap/), rc-o12-eis-constituents (RC/O12EisConst/), rc-o12-realize (RC/O12Realize/), rc-o12-formwise (RC/O12Formwise/), rc-o12-stage-val (RC/O12StageVal/), rc-two-fresh (h2fresh), rc-pm (P_M). Import existing modules; do not edit them.

Setup: your worktree is already on branch wip/rc-o12-stage-val at 40d619ca811e6d8e760c49ac7e273cf5be8b2272. Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). First step: git merge --no-edit 6e25b8c2efe22d4676d825c501b18734138deab8 (the head of wip/rc-pm; git merge-tree reports no conflict). Your files go under ZInQKernel/Contrib/OneProof/RC/O12StageVal/ (a new directory).

What exists (read first):
- RC/O12Theta/ (Inputs.lean: StageValuation, stage_source_symbol, fresh_input_of_stage, thetaData, inputs_of_stage; AtPrecision.lean: inputs_at_precision; Source.lean: lift_depth, lift_source; Symbol.lean: source_symbol_on_filter, source_symbol_off_support) and docs/research/rc-o12-theta.md.
- rc-pm's modules (RC/PM/, RC/AppF/Stage.lean) and its report docs/research/rc-pm.md, after the merge.
- RC/Odd/ (the odd-stage source, Divisions), RC/Symbols/ (the symbol, zero off its filter), RC/Stages/ and RC/Skeleton/ (the stage data and App G's depth and precision).
- The manuscript, diophantine_zq.tex, at the lines above.

Your work:
1. The stage identification: the same valid stage, good domain, budget, depth, admissibility and elliptic coefficients for the Odd data and the theta data (Divisions, the good-prime transfer, equality of a_p), with App G's depth and precision.
2. The P_M weights and lifts: instantiate the lift and stage inputs of rc-o12-theta from rc-pm's construction, including its finite-precision Brandt eigenrelation.
3. StageValuation: the intrinsic symbol and its integer representatives on the tested range, their depth and finite-precision phase comparison, and stage zero off the filter, from the tree's symbols and the stage data. Keep the (O.7) comparison data and its exact support as the named upstream ELLIOT input they are.
4. Apply inputs_at_precision with what you supplied, and list exactly what remains.
Out of scope for this run: (O.7) itself; the local blocks; the formwise hypotheses (rc-o12-formwise); the compatible realization (rc-o12-realize); h2fresh (rc-two-fresh).
Prints: only those already in the tree.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)). Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-o12-stage-val.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/O12StageVal/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-o12-stage-val.md and scratch/rc-o12-stage-val/. Do not use local notation; write abbreviations with explicit arguments, or inline (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom, and give #print axioms of each new theorem (only propext, Classical.choice and Quot.sound). The report docs/research/rc-o12-stage-val.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which input of inputs_at_precision (or of StageValuation and the lift and stage inputs) it supplies;
- the exact list of hypotheses that remain, each with its tex lines and its owner (sibling lane, ELLIOT input, or missing theory and its size);
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-o12-stage-val (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-o12-stage-val.md.

Output and commits: besides the report, keep a results log at scratch/rc-o12-stage-val/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-o12-stage-val.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-o12-stage-val.md last. Resuming: if scratch/rc-o12-stage-val/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-o12-stage-val.md is written and committed.
