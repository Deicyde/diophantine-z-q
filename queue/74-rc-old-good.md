rc-old-good: restrict BlockLevels.old_good to primes outside the stage's coefficient support, and re-prove the formwise consumers (base: wip/rc-blocks-per-u at 53109239c3236c49fbf9e308d946cdc066322884).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", then approved the project's hosts taking Theorem 5.3's appendices. The reviewer found that BlockLevels.old_good (RC/O12Formwise/, from rc-o12-formwise: ∀ q, T.Good q → q.Coprime oldLevel) is stronger than the text. A late-sieve prime or the current moving theta prime can divide the old level and still be T.Good (prime to T.m); tex 9471-9483 and 9670-9674 exclude exactly those primes (the coefficient support S: "every late sieve and the current moving theta prime") rather than declaring them bad. As stated, BlockLevels may be uninhabitable for the actual stage, and then hseed and hexcl would hold only vacuously downstream. rc-blocks-per-u (this base) constructs BlockLevels on its witnesses (realize_of_stage) and recorded the same issue. The reviewer asked for this fix before any fold. Do not overlap the sibling tasks: rc-aux-inputs (RC/AuxInputs/), rc-gz34-instance (RC/Gz34Instance/), rc-old-stage-law (RC/OldStageLaw/), rc-old-good (RC/OldGood/), rc-eis-slash (RC/EisSlash/); the reviewer's own briefs on the RCLeaves fields stage_support, even_upper, companion, address, calibration and base_zero; (3.5), which is on hold while the cloud root restates eq35; (O.7) (rc-o7-actual); PMLocal (rc-theta-join). Import existing modules; do not edit them.

Setup: your worktree is already on branch wip/rc-old-good at 53109239c3236c49fbf9e308d946cdc066322884 (the head of wip/rc-blocks-per-u). Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/OldGood/ (a new directory).

What exists (read first):
- RC/O12Formwise/ (BlockLevels, AtLevel, seed_level_coprime, seed_unramified, seed_fourier, window_good_hecke) and docs/research/rc-o12-formwise.md; RC/BlocksPerU/ (realize_of_stage, its construction of BlockLevels) and docs/research/rc-blocks-per-u.md, "Known issues".
- RC/O12Theta/ (InertiaOn, stated at good q ∉ support ∪ V'; buildWithFormwiseInertia; windowModel) and RC/O12/Build.lean (formwiseHecke_of_ambient).
- The manuscript, diophantine_zq.tex: 9471-9483, 9497-9555, 9670-9674, 9745-9750.

Your work:
1. Define BlockLevels' with old_good' : ∀ q, T.Good q → q ∉ S → q.Coprime oldLevel, where S is the stage's full coefficient support (the late sieves and the current moving theta prime included), and otherwise the same fields as BlockLevels.
2. Re-prove seed_level_coprime, seed_unramified, seed_fourier and window_good_hecke from BlockLevels' on the domain q ∉ S ∪ U, as new theorems in RC/OldGood/.
3. Check that InertiaOn's `support` is that S, or contains it, so that the downstream consumers (hseed, hexcl, good_hecke, buildWithFormwiseInertia) go through unchanged; prove the bridge. If the existing support does not contain the late sieves and the theta prime, report that first as the real mismatch, with the exact definitions, and stop.
4. Show that realize_of_stage's construction gives BlockLevels' (or say exactly what it needs), so the realization chain is not vacuous.
Out of scope for this run: OldStageLaw (rc-old-stage-law); the other laws; editing existing files.
Prints: none new.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)). Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-old-good.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/OldGood/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-old-good.md and scratch/rc-old-good/. Do not use local notation; write abbreviations with explicit arguments, or inline (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom, and give #print axioms of each new theorem (only propext, Classical.choice and Quot.sound). Any new structure or Prop that a theorem takes as a hypothesis must not restate the result it is used for: say in the report, for each one, why it is strictly weaker than the target and which manuscript step it is. The report docs/research/rc-old-good.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which consumer it re-proves on the restricted domain;
- the exact list of hypotheses that remain, each with its tex lines and its owner (sibling lane, ELLIOT input, or missing theory and its size);
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-old-good (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-old-good.md.

Output and commits: besides the report, keep a results log at scratch/rc-old-good/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-old-good.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-old-good.md last. Resuming: if scratch/rc-old-good/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-old-good.md is written and committed.
