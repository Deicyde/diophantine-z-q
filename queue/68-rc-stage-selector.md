rc-stage-selector: genus selections at the admissible parameters away from the witness, the stage-map selector extension (base: wip/rc-stage-map at f14a1399541c1b5ccb0228866e214694f44bd3f1).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", then approved the project's hosts taking Theorem 5.3's appendices. The host task rc-stage-map proved lamOf_admissible, which reads every comparison parameter once a genus datum is selected there. Its remaining row (docs/research/rc-stage-map.md, "Remaining hypotheses and interfaces") is ∀ θ D, W.admissible θ D → D ≠ Dw → (selG D).isSome, and it notes that the minimum, from the prepared filter alone, is Nonempty (HeegnerDatum E f Lat κ (D*hstar) 1 hstar) for each uncovered parameter, including the Heegner form and the algebraic realization of its parametrization value (tex 8209-8219, 9105-9113, 9272-9291, 9439-9443). The integrator approved this follow-up. Do not overlap the sibling tasks: rc-blocks-per-u (RC/BlocksPerU/), rc-eis-form (RC/EisForm/), rc-stage-ident (RC/StageIdent/), rc-stage-selector (RC/StageSelector/), rc-appg-coarse (RC/AppGCoarse/), and the project host one_proof1's rc-theta-join (the actual PMLocal, RC/O12StageVal/PM.lean) and pm-adelic-join (adelic level structures). Import existing modules; do not edit them.

Setup: your worktree is already on branch wip/rc-stage-selector at f14a1399541c1b5ccb0228866e214694f44bd3f1 (the head of wip/rc-stage-map). Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/StageSelector/ (a new directory).

What exists (read first):
- RC/StageMap/ (actualForStages, lamOf_admissible, chooseDatumEmbeddings) and docs/research/rc-stage-map.md.
- HeegnerDatum and its constructors (git grep 'structure HeegnerDatum' and its uses), the genus selection selG and the admissibility predicate (RC/Visibility/Genus.lean, RC/Visibility/Inputs.lean, RC/Wiring/OddModels.lean), RC/WitnessSpec/ (how the witness datum is built), RC/HeegnerAlgebra/ and RC/Rings/ (ring class fields, Heegner forms).
- The manuscript, diophantine_zq.tex: 2497-2530, 8209-8219, 9105-9113, 9265-9291, 9439-9443.

Your work:
1. Find how the witness datum's HeegnerDatum is built, and which of its inputs depend on D only through the conditions that admissibility gives (D a negative fundamental discriminant in the prepared filter, the Heegner condition at the level, the conductor-one order).
2. Build a HeegnerDatum at every admissible D the same way: the Heegner form for the conductor-one order of discriminant D·hstar, and the algebraic realization of its parametrization value. Define selG on those D and prove (selG D).isSome at every admissible nonwitness pair, keeping the witness entry unchanged.
3. If one ingredient needs new theory (for example the algebraicity of the parametrization value for a general D), state it as the smallest missing Prop, prove the rest, and stop.
Out of scope for this run: hcore and (O.7); the theta side; editing existing files (a new selector and a new instance variant in your files are fine).
Prints: only those already in the tree.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)). Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-stage-selector.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/StageSelector/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-stage-selector.md and scratch/rc-stage-selector/. Do not use local notation; write abbreviations with explicit arguments, or inline (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom, and give #print axioms of each new theorem (only propext, Classical.choice and Quot.sound). Any new structure or Prop that a theorem takes as a hypothesis must not restate the result it is used for: say in the report, for each one, why it is strictly weaker than the target and which manuscript step it is. The report docs/research/rc-stage-selector.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and how it supplies (selG D).isSome at the admissible nonwitness pairs, and which ingredient remains;
- the exact list of hypotheses that remain, each with its tex lines and its owner (sibling lane, ELLIOT input, or missing theory and its size);
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-stage-selector (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-stage-selector.md.

Output and commits: besides the report, keep a results log at scratch/rc-stage-selector/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-stage-selector.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-stage-selector.md last. Resuming: if scratch/rc-stage-selector/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-stage-selector.md is written and committed.
