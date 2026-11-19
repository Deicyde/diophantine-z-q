rc-appg-coarse: App G's coarse bound and attained minimum on the full intrinsic filter, from rc-o12-stage-val's remaining list (base: wip/rc-o12-stage-val at 9dcd60cd4e80c2ac528bfd1b03f4f68d29da15f8).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", then approved the project's hosts taking Theorem 5.3's appendices. The host task rc-o12-stage-val proved integerDepth_of_min, integerDepth_of_witness and integerDepth_of_data, which give IntegerDepth for the selected stage once App G's coarse bound holds and the depth is the minimum on the full intrinsic filter. Its report (docs/research/rc-o12-stage-val.md, row "Advancing precision, (F.5), and the minimum on the full intrinsic filter", tex 9385-9402, 9407-9445, 10151-10250) records that a minimum proved only on a narrower address filter does not supply this premise, and its Manuscript check marks tex 10175-10207 (the coarse bound and the fixed visible witness or attained minimum) unverified. The integrator approved this follow-up. Do not overlap the sibling tasks: rc-blocks-per-u (RC/BlocksPerU/), rc-eis-form (RC/EisForm/), rc-stage-ident (RC/StageIdent/), rc-stage-selector (RC/StageSelector/), rc-appg-coarse (RC/AppGCoarse/), and the project host one_proof1's rc-theta-join (the actual PMLocal, RC/O12StageVal/PM.lean) and pm-adelic-join (adelic level structures). Import existing modules; do not edit them.

Setup: your worktree is already on branch wip/rc-appg-coarse at 9dcd60cd4e80c2ac528bfd1b03f4f68d29da15f8 (the head of wip/rc-o12-stage-val). Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/AppGCoarse/ (a new directory).

What exists (read first):
- RC/O12StageVal/ (the depth lemmas and what they assume) and docs/research/rc-o12-stage-val.md, including its Known-issues note on the address filter versus the intrinsic filter.
- RC/Skeleton/ (App G's stages, precision and the existing finite-cutoff argument), RC/Symbols/ (coeffSymbol, the intrinsic filter), RC/Visibility/ (the fixed visible witness), RC/Odd/.
- The manuscript, diophantine_zq.tex: 9385-9445, 10151-10250 (App G).

Your work:
1. Prove App G's coarse bound on the full intrinsic odd filter: for each fixed budget, eventually T₀ ≤ M and min(T₀, δ + ω(n)) ≤ v₂ a(n) at every squarefree n on that filter, in the form integerDepth_of_min or integerDepth_of_witness takes.
2. Prove that the minimum is attained on the full intrinsic filter (or supply the fixed visible witness in the form integerDepth_of_witness needs), not on the narrower address filter.
3. Apply integerDepth_of_data, and list exactly what remains.
Out of scope for this run: (O.7); the sieve and squarefree support; the stage identification (rc-stage-ident).
Prints: only those already in the tree.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)). Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-appg-coarse.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/AppGCoarse/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-appg-coarse.md and scratch/rc-appg-coarse/. Do not use local notation; write abbreviations with explicit arguments, or inline (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom, and give #print axioms of each new theorem (only propext, Classical.choice and Quot.sound). Any new structure or Prop that a theorem takes as a hypothesis must not restate the result it is used for: say in the report, for each one, why it is strictly weaker than the target and which manuscript step it is. The report docs/research/rc-appg-coarse.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which premise of the depth lemmas it supplies;
- the exact list of hypotheses that remain, each with its tex lines and its owner (sibling lane, ELLIOT input, or missing theory and its size);
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-appg-coarse (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-appg-coarse.md.

Output and commits: besides the report, keep a results log at scratch/rc-appg-coarse/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-appg-coarse.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-appg-coarse.md last. Resuming: if scratch/rc-appg-coarse/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-appg-coarse.md is written and committed.
