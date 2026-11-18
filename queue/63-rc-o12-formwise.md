rc-o12-formwise: the formwise ramification and good-Hecke comparisons for (O.12), the hypotheses hseed and hexcl of rc-o12-theta (base: rc/thm53-proof-20261117 at 40d619ca811e6d8e760c49ac7e273cf5be8b2272).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", then approved the project's hosts taking Theorem 5.3's appendices. The host task rc-o12-theta separated the stationary Kummer support from the ambient Hecke exclusions by formwise inertia (formwise_kummer, buildWithFormwiseInertia), leaving two named hypotheses (docs/research/rc-o12-theta.md, "Remaining hypotheses", row "Formwise ramification of the seed and good Hecke outside the ambient test"): hseed, that at q outside the support and U, inertia fixes every constituent occurring in each seed indexed by a subset of U; and hexcl, the good Fourier formula for F_U alone at a good q not in U that the ambient Hecke tests exclude. The missing pieces are formwise level and attachment comparisons. The root folded rc-o12-local, rc-o12-eisenstein, rc-o12-theta and rc-theta-coeff into this base at e89673d3a (their reports are in docs/research/). The lead approved this follow-up. Do not overlap the sibling tasks: rc-stage-map (RC/StageMap/), rc-o12-eis-constituents (RC/O12EisConst/), rc-o12-realize (RC/O12Realize/), rc-o12-formwise (RC/O12Formwise/), rc-o12-stage-val (RC/O12StageVal/), rc-two-fresh (h2fresh), rc-pm (P_M). Import existing modules; do not edit them.

Setup: your worktree is already on branch wip/rc-o12-formwise at 40d619ca811e6d8e760c49ac7e273cf5be8b2272. Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/O12Formwise/ (a new directory).

What exists (read first):
- RC/O12Theta/ (Model.lean: formwise_kummer, buildWithFormwiseInertia; Window.lean: windowModel; Inputs.lean: inputs_of_stage) and docs/research/rc-o12-theta.md.
- RC/ThetaCoeff/ (Model.lean: Blocks.build and inertia_le_consN_of_seed; Blocks, Forms, Hecke, Operators, Lattice) and docs/research/rc-theta-coeff.md: the realization Blocks and Attachment (ELLIOT) and the good cuspidal polynomial from Carayol already used there.
- RC/O12/Build.lean (formwiseHecke_of_ambient: its remaining comparison is confined to the primes excluded from the ambient test).
- The manuscript, diophantine_zq.tex: 9660-9668, 9670-9674, 9745-9750, 9754-9769.

Your work:
1. A formwise conductor and attachment lemma: for each seed indexed by a subset of U, the constituents occurring in it are unramified at every good q outside the support and U, with the good polynomial on the active coordinates. This gives hseed.
2. The corresponding Fourier operator on the form: the good Fourier formula for F_U alone at a good q not in U excluded from the ambient tests. This gives hexcl, and with formwiseHecke_of_ambient the good_hecke field.
3. Use the existing realization (Blocks, Attachment) and its level data. Where the text asserts a step without a citation, it is ELLIOT and becomes a named hypothesis if you cannot prove it.
Out of scope for this run: the compatible realization across tested sets (rc-o12-realize), the local blocks at p (rc-o12-local, rc-o12-eisenstein, rc-o12-eis-constituents), the stage valuation (rc-o12-stage-val).
Prints: only those already in the tree (Carayol's good polynomial as already used).

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)). Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-o12-formwise.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/O12Formwise/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-o12-formwise.md and scratch/rc-o12-formwise/. Do not use local notation; write abbreviations with explicit arguments, or inline (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom, and give #print axioms of each new theorem (only propext, Classical.choice and Quot.sound). The report docs/research/rc-o12-formwise.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which of hseed, hexcl or good_hecke it supplies;
- the exact list of hypotheses that remain, each with its tex lines and its owner (sibling lane, ELLIOT input, or missing theory and its size);
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-o12-formwise (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-o12-formwise.md.

Output and commits: besides the report, keep a results log at scratch/rc-o12-formwise/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-o12-formwise.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-o12-formwise.md last. Resuming: if scratch/rc-o12-formwise/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-o12-formwise.md is written and committed.
