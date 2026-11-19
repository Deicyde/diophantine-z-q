rc-gz34-instance: the GenusOdd instance behind (3.4) at the rough companions (base: wip/rc-stage-selector at 56ff832825d5debcba47505977b8b9ecd95a925a).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", then approved the project's hosts taking Theorem 5.3's appendices. (3.4) (Gz34Target and its first clause Gz34CompAt, RC/Wiring/Data.lean and FinalFamily.lean; tex 2411-2440, 10172-10178) is PROVED by gz34Target_of_genusOdd (RC/Wiring/GenusOdd34.lean) from Prints, ArtinFactorization, the root numbers and one GenusOddInstance W: the newform f with the L-function coefficients, the lattice and its non-CM property, the parametrization scale κ, RC11's normalization of L_* and its identification with W.Lstar, the Birch–Manin/Manin–Drinfeld rationality hElkikMD, the genus partner, the genus and ring-class selections selG and selR with their isSome conditions, the identifications hjg and hjr of W.jgen and W.jrc with the indices read off those selections, hprep, hcomp, and the final k's conditions. rc-stage-selector (this base) built genus selections at every admissible parameter (extendSelG, exists_selected_of_admissible) up to PreparedParamValue. The integrator and the reviewer approved this task. Do not overlap the sibling tasks: rc-aux-inputs (RC/AuxInputs/), rc-gz34-instance (RC/Gz34Instance/), rc-old-stage-law (RC/OldStageLaw/), rc-eis-slash (RC/EisSlash/); the reviewer's own briefs on the RCLeaves fields stage_support, even_upper, companion, address, calibration and base_zero; (3.5), which is on hold while the cloud root restates eq35; (O.7) (rc-o7-actual); PMLocal (rc-theta-join). Import existing modules; do not edit them.

Setup: your worktree is already on branch wip/rc-gz34-instance at 56ff832825d5debcba47505977b8b9ecd95a925a (the head of wip/rc-stage-selector). Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/Gz34Instance/ (a new directory).

What exists (read first):
- RC/Wiring/GenusOdd34.lean (GenusOddInstance, gz34Target_of_genusOdd and the lemmas before it), RC/Wiring/Data.lean, RC/Wiring/FinalFamily.lean (Gz34CompAt), RC/Wiring/Leaves.lean (where the instance is consumed).
- ZInQKernel/Contrib/CloudB3RC53/GenusOdd/ and CST/ (HeegnerDatum, jgenOf, jrcOf, Prepared, Companion, GenusPartner), the newform and lattice data already in the tree (git grep newformLevel, IsLatticeOf, IsParamScale, CentralNormalization).
- RC/StageSelector/ and RC/StageMap/ (this base) and their reports.
- The manuscript, diophantine_zq.tex: 1825-1830, 2404-2440, 7175-7177, 10172-10178.

Your work:
1. List the fields of GenusOddInstance and, for each, whether the tree already supplies it for the actual curve E_ℓ (newform from modularity, lattice, non-CM, κ, normalization), what supplies it, or what is missing.
2. Build the ring-class selections selR at every prepared h and companion k', the analogue of rc-stage-selector's genus selections, up to the same parametrization-value input; prove hselG and hselR.
3. Construct the instance, with the remaining genuinely missing inputs (for example hElkikMD, or PreparedParamValue) as named hypotheses, and apply gz34Target_of_genusOdd to get Gz34CompAt (and Gz34Target).
Out of scope for this run: (3.5); (F.3) (rc-aux-inputs); the theta side.
Prints: only those already in the tree. hElkikMD is stated in the tree as an input; do not add a new print for it, keep it named.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)). Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-gz34-instance.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/Gz34Instance/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-gz34-instance.md and scratch/rc-gz34-instance/. Do not use local notation; write abbreviations with explicit arguments, or inline (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom, and give #print axioms of each new theorem (only propext, Classical.choice and Quot.sound). Any new structure or Prop that a theorem takes as a hypothesis must not restate the result it is used for: say in the report, for each one, why it is strictly weaker than the target and which manuscript step it is. The report docs/research/rc-gz34-instance.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which field of GenusOddInstance it supplies;
- the exact list of hypotheses that remain, each with its tex lines and its owner (sibling lane, ELLIOT input, or missing theory and its size);
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-gz34-instance (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-gz34-instance.md.

Output and commits: besides the report, keep a results log at scratch/rc-gz34-instance/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-gz34-instance.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-gz34-instance.md last. Resuming: if scratch/rc-gz34-instance/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-gz34-instance.md is written and committed.
