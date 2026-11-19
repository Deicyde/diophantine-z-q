rc-eis-form: the weight-two Eisenstein character-pair form, its expansion and its occurrence, the scoped stop of rc-o12-eis-constituents (base: wip/rc-o12-eis-constituents at 007d8d6d06a70c116f2f310b426406f2c6017b0b).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", then approved the project's hosts taking Theorem 5.3's appendices. The host task rc-o12-eis-constituents proved realized_branch (eisenstein_branch's clause from the actual constituent data), ColumnRealization.expansion and RepInput.split, and stopped at three named inputs (docs/research/rc-o12-eis-constituents.md): the existence and positive expansion of the primitive weight-two form of the character pair, the labeled occurrence of those forms in the theta blocks, and the corresponding good-prime attachment. The integrator approved this follow-up. Do not overlap the sibling tasks: rc-blocks-per-u (RC/BlocksPerU/), rc-eis-form (RC/EisForm/), rc-stage-ident (RC/StageIdent/), rc-stage-selector (RC/StageSelector/), rc-appg-coarse (RC/AppGCoarse/), and the project host one_proof1's rc-theta-join (the actual PMLocal, RC/O12StageVal/PM.lean) and pm-adelic-join (adelic level structures). Import existing modules; do not edit them.

Setup: your worktree is already on branch wip/rc-eis-form at 007d8d6d06a70c116f2f310b426406f2c6017b0b (the head of wip/rc-o12-eis-constituents). Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/EisForm/ (a new directory).

What exists (read first):
- RC/O12EisConst/ (Forms, Galois, Branch) and docs/research/rc-o12-eis-constituents.md; RC/O12Eisenstein/ (DivisorSum, Characters, LocalBlocks).
- Mathlib's Eisenstein series (ModularForms.EisensteinSeries) and Dirichlet characters, and anything in the tree on Eisenstein series with character (git grep Eisenstein).
- The manuscript, diophantine_zq.tex: 9647-9654, 9754-9771, 9852-9873.

Your work:
1. The existence and expansion: for the character pair (χ₁, χ₂) the constituents use, construct the weight-two Eisenstein series E(χ₁, χ₂) with q-expansion coefficients σ(χ₁, χ₂; n) = Σ_{d | n} χ₁(n/d) χ₂(d) d, from Mathlib's Eisenstein series where possible, and prove the positive-coefficient expansion the named input asks for. If modularity at the exact level with character is not available, prove the coefficient identity on the q-expansion side and state modularity as the smallest missing Prop.
2. The good-prime attachment: the representation χ₁ ⊕ χ₂·(cyclotomic) has Frobenius trace σ(χ₁, χ₂; q) and the right determinant at good q. This is algebra on characters; prove it.
3. The labeled occurrence in the theta blocks depends on the block realization (rc-blocks-per-u). State exactly what it needs from that realization, and prove the occurrence conditionally on it.
Out of scope for this run: the cuspidal blocks; the realization of the theta blocks (rc-blocks-per-u); changing the constituent model.
Prints: only those already in the tree.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)). Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-eis-form.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/EisForm/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-eis-form.md and scratch/rc-eis-form/. Do not use local notation; write abbreviations with explicit arguments, or inline (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom, and give #print axioms of each new theorem (only propext, Classical.choice and Quot.sound). Any new structure or Prop that a theorem takes as a hypothesis must not restate the result it is used for: say in the report, for each one, why it is strictly weaker than the target and which manuscript step it is. The report docs/research/rc-eis-form.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which of the three named inputs of rc-o12-eis-constituents it supplies;
- the exact list of hypotheses that remain, each with its tex lines and its owner (sibling lane, ELLIOT input, or missing theory and its size);
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-eis-form (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-eis-form.md.

Output and commits: besides the report, keep a results log at scratch/rc-eis-form/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-eis-form.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-eis-form.md last. Resuming: if scratch/rc-eis-form/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-eis-form.md is written and committed.
