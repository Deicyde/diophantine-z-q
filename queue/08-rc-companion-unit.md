rc-companion-unit: choose the final companion as the manuscript does. Construct k as a unit of a separate even symbol on negative discriminants (tex 2595-2603), prove every conjunct of CompanionLeaf for that k, and prove rc-ksplit-old-unit's certificate CompanionOldUnit for the same k (base: wip/rc-ksplit-old-unit at 2891c386b07f8540d57c24a17b893b364ee1f75c).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", and the standing goal is to reduce the manuscript to the literature it cites. The text says, verbatim (tex 2595-2599): "Use a separate even symbol on negative discriminants square at 2N, excluding the fixed odd support, the ramification support of E[8], and the exceptional imaginary fields. Choose a unit k of this symbol. Then L(E^(k),1)≠0." The tree's provider does something else. CloudB3RC53.Companion.exists_companion picks a twist with L(E^(k),1) ≠ 0 from the prints HoffsteinLuo and BFHTwistSign (via genusPartner) and never makes k a unit of any symbol. Two host tasks hit the consequence. rc-even-reading flagged that the companion leaf does not certify k as a unit of the old source. rc-ksplit-old-unit (docs/research/rc-ksplit-old-unit.md) proved the whole transported lower bound conditional only on that one-index certificate, CompanionOldUnit O W.kfin, and proved that such a k exists (exists_companionOldUnit). Following the text closes the certificate, and it may remove two analytic prints from the companion. The project claims this on fork issue #83.
Do not overlap:
- the odd-minimum preservation (tex 2609-2612, 10519-10521; the CompanionLeaf order-of-choices departure);
- rc-even-place2 (the coefficient place);
- the genus partner h_* (genusPartner's use for h_* stays as it is).
Import existing modules; do not edit them. Produce a provider the integrator can wire, and do not edit RC/Wiring/.

Setup: your worktree is already on branch wip/rc-companion-unit at 2891c386b07f8540d57c24a17b893b364ee1f75c. Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/CompanionUnit/ (a new directory).

What exists (read first):
- docs/research/rc-ksplit-old-unit.md and RC/KSplitOldUnit/ (OldSource, oldSource_of_phase, exists_companionOldUnit, companionOldUnit_iff, old_transport_inputs, transported_lower_of_companion_old_unit, oldRetained_of_companion_avoidance), especially its Known issues: the old support must be the pre-companion support.
- RC/Wiring/CompanionLeaf.lean (CompanionLeaf and its conjuncts, companionTarget_of), CloudB3RC53/Companion/Leaf.lean (exists_companion, companionLeaf_of), CloudB3RC53 genusPartner and its prints.
- RC/AppE/ (evenPhaseData_of_prints, the attained minimum, (E.9)-(E.11)), RC/AuxInputs/ (sourceFamily_of_prints), RC/EvenReading/ (genuineEvenSource_for_labels).
- The manuscript, diophantine_zq.tex: 2584-2612, 7780-7808 ((E.9), forward rank zero), 8130-8145 ((E.10)-(E.11)), 10255-10320.

Your work:
1. The separate even symbol: build the old source O (oldSource_of_phase) on negative discriminants with the initial filter of tex 2595-2597: square at every prime of 2N, excluding the fixed odd support, the ramification support of E[8], and the exceptional imaginary fields (k ≠ -1, -3), and coprime to h_*. Use the pre-companion support, as the ksplit report requires.
2. Choose k as a unit of O (exists_companionOldUnit on this filter). Prove CompanionOldUnit O k.
3. Prove the conjuncts of CompanionLeaf for k: k < 0, squarefree, k ≠ -1, -3, k ≡ 1 mod 4, a unit square at 2N, IsCoprime k h_*, and L_*(k) ≠ 0. The last is the text's "Then L(E^(k),1)≠0", from the unit and (E.11) with the nonzero reference (old_transport_inputs already gives C.Lstar k ≠ 0). The support conjunct (primes of k in W.S) belongs to the final support after k is fixed; state how the provider builds W.S from the pre-companion support plus the primes of k.
4. tex 2599-2601: "At least one prime ramified in K is outside all the old fixed label extensions and torsion ramification." Prove it for this k, or state it exactly as the one remaining input.
5. Package a provider of CompanionLeaf W together with CompanionOldUnit O W.kfin for the same W, and say whether HoffsteinLuo or BFHTwistSign is still needed for the companion (it should not be). List what remains, with owners.
Out of scope for this run:
- the odd minimum and the order of choices;
- the genus partner;
- editing existing files.
Prints: none new.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)) in the report. Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-companion-unit.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/CompanionUnit/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-companion-unit.md and scratch/rc-companion-unit/. Do not use local notation; write abbreviations with explicit arguments (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom. Run #print axioms of each new theorem from a check file under scratch/rc-companion-unit/, not in the deliverable files (only propext, Classical.choice and Quot.sound), and list the results in the report. The report docs/research/rc-companion-unit.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which conjunct of CompanionLeaf or which certificate (CompanionOldUnit) it supplies;
- the exact list of remaining hypotheses with their owners, and whether HoffsteinLuo and BFHTwistSign are still used anywhere after this, and where;
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-companion-unit (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-companion-unit.md.

Output and commits: besides the report, keep a results log at scratch/rc-companion-unit/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-companion-unit.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-companion-unit.md last. Resuming: if scratch/rc-companion-unit/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-companion-unit.md is written and committed.

Build note (read before compiling): the worktree's .lake was copied from a build of the fork's main, so modules that exist only on your base branch (or arrive with your merge) have no .olean yet, and lake env lean on a file that imports them stops with a missing-object error. Before checking your own files, build their imports once with lake build <Module> for each module your files import (one Lean process at a time; let each finish), then compile your files. Never report a file as unchecked because an import was not built: build it. Report any file that still fails, with the error.
