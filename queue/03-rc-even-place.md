rc-even-place: one coefficient place for the even source. Construct rc-even-budget's SourceAtPlace for the actual App E source, keeping the two-power order of the character, together with the characteristic-zero coefficient ring that rc-ksplit-seed asks for and the integrality of the tested singleton divisions (base: wip/rc-even-budget at 55d1aaa2328e8a12567ed5cc5781980054b0e78b, merged with wip/rc-ksplit-seed at 66fe8821b465fc3afc80f40b42acfe1192ec9794).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", and the standing goal is to reduce the manuscript to the literature it cites. rc-even-budget (docs/research/rc-even-budget.md) and rc-ksplit-seed (docs/research/rc-ksplit-seed.md) both stop first at the same coefficient-place input. For rc-even-budget it is Nonempty (SourceAtPlace P O K) over one number field with its embedding at two, integral lifts of the character and the squarefree phases, and ∀ p good, ∃ t, η(p)^(2^t) = 1; the abstract EvenPhaseData dropped the character order, which the App E producer has (AppE.eta_pow_two_pow_eq_one). For rc-ksplit-seed it is O : Subring ℂ with odd denominators inverted and 1/2 ∉ O, the phases z_n and η(n) in O, and H_p ∈ O at each tested singleton. These are one coefficient realization, not separate choices at each U. The analytic realization of the even weight-two forms is a separate, larger task and is out of scope. The project claims this on fork issue #83.
Do not overlap:
- the even analytic realization (the all-index expansion identity on weight-two forms);
- the constituent and local-block lanes;
- rc-ksplit-old-unit (the old-unit comparison);
- the address integrator's choice of modulus.
Import existing modules; do not edit them.

Setup: your worktree is already on branch wip/rc-even-place at 55d1aaa2328e8a12567ed5cc5781980054b0e78b. First run git merge --no-edit 66fe8821b465fc3afc80f40b42acfe1192ec9794 (the commits are already in the local repository, and they merge cleanly in this order). Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/EvenPlace/ (a new directory).

What exists (read first):
- RC/EvenBudget/ (Place.lean: SourceAtPlace; Source.lean, Divided.lean, Valuation.lean, Realization.lean: budgetRealization_of_blocks) and its report, section "Remaining hypotheses", first row.
- RC/KSplitSeed/ (Sieve.lean: evenCoeff, evenCoeff_squarefree, evenCoeff_shell, transported_lower_of_old_unit; Valuation.lean: ratCast_pow_two_factor, evenCoeff_factor_of_no_reading, dirichletValue_unit_of_coprime; Seed.lean: kSplitSeed_of_singleton_trace) and its report, rows 2 and 3 of the remaining table.
- RC/AppE/Assembly.lean (evenPhaseData_of_prints, evenPhaseData_of_prints_levelFilter, eta_pow_two_pow_eq_one) and RC/AppE/ (the (E.10)-(E.12) square comparison and the recurrence), RC/AuxInputs/ (sourceFamily_of_prints), RC/LocalWeights/ (coefficientRing, coefficientRing_two).
- The manuscript, diophantine_zq.tex: 7943-7944, 8040-8082, 8130-8189 ((E.10)-(E.12) and the recurrence, with the normalization note at 8162-8167, ledger N4), 8136-8145, 9638-9643, 9649-9652, 10332-10344.

Your work, for the actual even source produced by AppE.evenPhaseData_of_prints (one source P per total type, as in AuxInputs.sourceFamily_of_prints):
1. The character order: carry η's two-power order from the App E producer through to the source. If EvenPhaseData forgot it, give a variant producer (new file) that keeps it, and prove that it agrees with the original on every other field.
2. SourceAtPlace: one number field K containing the values of η, ψ and the phases z_D (tex 8130-8145: z_D is a two-power root of unity, r_D is rational), a ring O with its prime above two, the embedding at two, and integral lifts. Build Nonempty (SourceAtPlace P O K) for the actual P.
3. The ksplit ring: from the same K, give O : Subring ℂ (through a fixed complex embedding of K) with hodd, hhalf, hz and hηO, as rc-ksplit-seed's kSplitSeed_of_singleton_trace takes them. It must be the same place as step 2.
4. The singleton divisions: H_p n ∈ O for every tested singleton p and every n (the exact integer divisions (O.9)-(O.11) at depth zero, tex 10337-10344, 9450-9455), from the shell recurrence (proved: evenCoeff_shell) and the lower bound. If the lower bound is needed, take transported_lower_of_old_unit's output as a parameter (rc-ksplit-old-unit owns it).
5. State which inputs of budgetRealization_of_blocks and kSplitSeed_of_singleton_trace remain after this, with owners.
Out of scope for this run:
- the even weight-two analytic realization and the formwise, constituent and local data;
- the old-unit comparison;
- editing existing files.
Prints: none new.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)) in the report. Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-even-place.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/EvenPlace/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-even-place.md and scratch/rc-even-place/. Do not use local notation; write abbreviations with explicit arguments (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom. Run #print axioms of each new theorem from a check file under scratch/rc-even-place/, not in the deliverable files (only propext, Classical.choice and Quot.sound), and list the results in the report. The report docs/research/rc-even-place.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which input of budgetRealization_of_blocks or kSplitSeed_of_singleton_trace it supplies;
- the exact list of remaining hypotheses with their owners;
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-even-place (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-even-place.md.

Output and commits: besides the report, keep a results log at scratch/rc-even-place/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-even-place.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-even-place.md last. Resuming: if scratch/rc-even-place/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-even-place.md is written and committed.
