rc-ksplit-old-unit: the old-unit comparison behind the transported lower bound. Discharge the inputs hOldk, hUnit, hOld and hOldLow of rc-ksplit-seed's transported_lower_of_old_unit on the exact old source and the companion's k, so the lower bound ω(n) ≤ v₂ r(n) on the new filter holds without an assumed comparison (base: wip/rc-ksplit-seed at 66fe8821b465fc3afc80f40b42acfe1192ec9794).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", and the standing goal is to reduce the manuscript to the literature it cites. rc-ksplit-seed (docs/research/rc-ksplit-seed.md, the first row of "Exact remaining hypotheses and owners") proved KSplitSeed for the address's even reading, conditional on that comparison: a common nonzero reference L_ref, L_*(k) ≠ 0, k.natAbs.primeFactors ⊆ S, the old square comparisons at d_k and d_k D ((E.11) on the exact old source), the old unit at d_k, and the old lower bound at retained d_k D. Its report notes: "The current companion identifies a nonzero reference and exclusions; it does not identify the valuation of its old coefficient with the old minimum." The manuscript step is tex 10260 and 10293-10314. It is also the flag rc-even-reading raised (the companion leaf does not certify that k was a unit of the old source). The project claims this on fork issue #83.
Do not overlap:
- rc-even-place (the coefficient place and ring);
- the companion leaf itself (RC/Wiring/CompanionLeaf.lean: do not edit it; if it lacks the old-unit certificate, state the smallest addition it needs as a named hypothesis and report it for the root);
- Appendix E's Kato step.
Import existing modules; do not edit them.

Setup: your worktree is already on branch wip/rc-ksplit-old-unit at 66fe8821b465fc3afc80f40b42acfe1192ec9794. Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/KSplitOldUnit/ (a new directory).

What exists (read first):
- RC/KSplitSeed/Sieve.lean (transported_lower_of_old_unit and its four hypotheses; transport_valuation; revGen_empty; evenCoeff_squarefree), RC/KSplitSeed/Valuation.lean, and the report.
- RC/Wiring/CompanionLeaf.lean (CompanionLeaf, CompanionTarget, the order-of-choices departure note), RC/Skeleton/Steps.lean, RC/AddressGenuine/ (AddressDensityLeafGenuineEven, EvenReading), RC/EvenReading/ (on wip/rc-even-reading; its report's flag (a)).
- RC/AppE/ (the square comparison (E.10)-(E.11) and its proof), RC/AuxInputs/ (sourceFamily_of_prints, the old source at its fixed minimum depth).
- The manuscript, diophantine_zq.tex: 2584-2612 (the companion construction and the odd minimum), 8130-8145 ((E.10)-(E.11)), 10255-10320 (the transported source and its lower bound), 10519-10521.

Your work:
1. The square comparisons (hOldk, hOld side): on the exact old source, prove the rational square identities at d_k and d_k D with the common reference, from App E's (E.11) as proved in the tree. Identify which source and normalization the transport uses (tex 10293-10314), and check that it is the one App E produced.
2. The alignment: d_k D stays in the old retained filter (D is a square unit at the old support), from the prepared filter and the companion's avoidance set. Cite the tex lines that give it.
3. The old unit at d_k (hUnit) and the old lower bound at retained d_k D (hOldLow): derive them from the companion's construction and the old even source's minimum (tex 2584-2612, 10260). If the companion leaf as stated does not give that k was a unit of the old source, do not assume it silently. State the exact certificate the companion leaf would have to carry, and argue that it is strictly weaker than CompanionLeaf's target (or say that it is not).
4. Apply transported_lower_of_old_unit and list what remains, with owners.
Out of scope for this run:
- the coefficient place (rc-even-place);
- editing existing files, including the companion leaf;
- the odd case.
Prints: none new.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)) in the report. Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-ksplit-old-unit.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/KSplitOldUnit/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-ksplit-old-unit.md and scratch/rc-ksplit-old-unit/. Do not use local notation; write abbreviations with explicit arguments (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom. Run #print axioms of each new theorem from a check file under scratch/rc-ksplit-old-unit/, not in the deliverable files (only propext, Classical.choice and Quot.sound), and list the results in the report. The report docs/research/rc-ksplit-old-unit.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which hypothesis of transported_lower_of_old_unit it supplies;
- the exact list of remaining hypotheses with their owners, and for any certificate asked of the companion leaf, why it is strictly weaker than its target;
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-ksplit-old-unit (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-ksplit-old-unit.md.

Output and commits: besides the report, keep a results log at scratch/rc-ksplit-old-unit/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-ksplit-old-unit.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-ksplit-old-unit.md last. Resuming: if scratch/rc-ksplit-old-unit/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-ksplit-old-unit.md is written and committed.
