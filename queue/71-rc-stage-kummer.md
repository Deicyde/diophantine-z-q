rc-stage-kummer: one actual stage map for every evaluated genus datum. Construct the shared StageKummer used by lamOf as reduction at the chosen place followed by λ_M, prove that it satisfies the witness pin OddStagedInstance.hev, and supply the premise hev of PMGeometry.lamOf_reduction_at at every selected (θ, D, dat) on the inert support (base: wip/pm-adelic-join at bfcc02719fbc32c406d354ad6eb5a4c87cdf943e, merged with wip/rc-stage-ident at c2bb312793a4de6142f0695d87961aeb7edf6e2e, wip/rc-stage-selector at 56ff832825d5debcba47505977b8b9ecd95a925a and wip/rc-o7-actual at e374fbb3d89b0c04ff7e7ba53e1902d769fb31bd).

Why: the owner said "I feel like we're spending way too much time re-reading literature and not nearly enough time trying to prove Elliot's manuscript", and the standing goal is to reduce the manuscript to the literature it cites. In the tree, the stage maps ev : Visibility.StageKummer (RC/Visibility/Genus.lean:168) are a free family: OddStagedInstance.hev (RC/Wiring/StageData.lean:241) pins only the entry at the fixed witness D_w, and exists_pinned_stageKummer (RC/Wiring/StageDataNonVacuity.lean:297) shows the other entries are unconstrained. The manuscript uses one map everywhere: reduction at the chosen place above ℓ₀ followed by λ_M (tex 8378-8398, 8439-8456, 8476, 9283-9291). The host task pm-adelic-join (report docs/research/pm-adelic-join.md, section "Heegner scope") found that the (O.7) reference reduction needs exactly this agreement at each evaluated datum: lamOf_reduction_at (RC/PMGeometry/Heegner.lean:133) takes hev : ev θ D dat = (PM.lam d).comp (datumReduction dat v w hg). This is a Lean-side gap, not a manuscript step, and closing it removes a free choice from the odd chain. The project claims it on fork issue #83.
Do not overlap:
- rc-o7-orbits and rc-o7-character (the orbit fibers, torus weights and the genus character);
- rc-theta-join (PMLocal);
- the two pointwise CM inputs of pm-adelic-join's Heegner scope (the reductions of the CM conjugates equal C(z), tex 9265-9279; π(r_c) = datumReduction_v(σ_c y), tex 8476-8479 and 9283-9291). They stay named inputs.
Import existing modules; do not edit them.

Setup: your worktree is already on branch wip/rc-stage-kummer at bfcc02719fbc32c406d354ad6eb5a4c87cdf943e. First run git merge --no-edit c2bb312793a4de6142f0695d87961aeb7edf6e2e, then git merge --no-edit 56ff832825d5debcba47505977b8b9ecd95a925a, then git merge --no-edit e374fbb3d89b0c04ff7e7ba53e1902d769fb31bd (the commits are already in the local repository, and they merge cleanly in this order). Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Your files go under ZInQKernel/Contrib/OneProof/RC/StageKummer/ (a new directory).

What exists (read first):
- docs/research/pm-adelic-join.md ("Heegner scope"), docs/research/rc-stage-ident.md, docs/research/rc-stage-selector.md, docs/research/rc-stage-map.md, docs/research/rc-o7-actual.md (the reduce field of DatumAt and the row for rc-stage-ident and rc-stage-selector).
- RC/Visibility/Genus.lean: StageKummer, lamOf, lamOf_native_bound.
- RC/PMGeometry/Heegner.lean: DatumPlace (emb, inert), datumReduction, lamOf_reduction_at. RC/PMGeometry/Evaluation.lean: stageMap_eq_lam_comp.
- RC/Wiring/StageData.lean: OddModels, OddStagedInstance (hev, hstages), witnessSpecialization. RC/Wiring/StageWitness.lean: actualRingClassRed, actualStageMapOn. RC/Wiring/StageDataNonVacuity.lean: StageKummer.pinAt, exists_pinned_stageKummer.
- RC/StageIdent/: selectedEvaluation_lam, selectedEvaluationOn_lam, detectorAt_lam (PM.lam of the selected evaluation is StageMap.actualEvaluations.eval i, on all points). RC/StageSelector/: extendSelG, extendSelG_isSome_of_admissible. RC/StageMap/: actualForStages, lamOf_admissible.
- The manuscript, diophantine_zq.tex: 8370-8398 and 8439-8459 (the stage map, the place above ℓ₀, the residue field 𝔽_{ℓ₀²}, λ_M = b ∘ κ_M); 8476 and 9283-9291 (the same map read on the genus points); 2512-2530 and 9112-9113 (λ_θ(D)).

Your work:
1. For each stage θ and each selected genus datum dat at D with (D/ℓ₀) = 1, give a DatumPlace at the stage's place: a compatible embedding of the ring class field into ℚ̄ and the inertness of ℓ₀ in dat.K (tex 9207: (Dh_*/ℓ₀) = -1). Say which embedding is chosen, and why it is the one the manuscript's "chosen place" fixes. It must restrict to the detector's place on the base field.
2. Define the actual family evActual : StageKummer by evActual θ D dat = (PM.lam d_θ).comp (datumReduction dat v w hg) on the inert support, where d_θ is the stage's PM.Evaluation from rc-stage-ident. Off the inert support, choose a value and document it; lamOf there is not read by (O.7).
3. Prove the witness pin: evActual satisfies OddStagedInstance.hev at D_w, i.e. it agrees with actualStageMapOn at the selected witness datum. Use stageMap_eq_lam_comp, detectorAt_lam and actualRingClassRed. If the split twist row has to be aligned with the detector at the witness, prove the alignment; do not assume it.
4. Supply hev of lamOf_reduction_at for evActual at every selected (θ, D, dat) on the inert support. Then state the reference reduction of rc-o7-actual (the reduce field of DatumAt) as conditional only on the two pointwise CM inputs and the orbit data, with everything else discharged.
5. Give an OddStagedInstance (or the smallest wrapper the wiring accepts) with ev := evActual, so that downstream consumers use the actual map rather than a pinned free family. List any wiring field that this changes.
State exactly which hypotheses remain, with owners, and argue that each is strictly weaker than (O.7) and does not restate it.
Out of scope for this run:
- the two pointwise CM inputs above (they stay named; the reviewer is deciding separately whether the first becomes a printed form of the Cornut-Jetchev citation);
- OrbitFibers, TorusWeights, Normalizers;
- the algebraic realization of the genus parametrization values (rc-stage-selector's remaining input);
- editing existing files.
Prints: none new.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Label any step that is in neither as on-the-spot (provenance (c)) in the report. Cited prints become printed-form leaves exactly as Elliot uses them (the owner's Gross-Zagier ruling: "Follow the manuscript: CST Thm 1.1 and Kolyvagin Thm 1 become printed-form leaves exactly as Elliot cites them; we write no GZ argument of our own"). Reuse the print statements already in the tree (RC/PrintsArith, RC/PrintsAnalytic, RC/AppF/Prints.lean, the shared layer's Prints) and add only the prints named in this brief. No network is needed and you have none: mark page and theorem numbers you give from memory UNVERIFIED. If a source has a known issue, document it. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/rc-stage-kummer.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

The stop rule, for this unattended run: if a step needs a large missing theory, build only the minimal faithful pieces the next step needs. Otherwise finish what can be finished and write a scoped report: what is missing, how large it is, the smallest faithful statement of it, and what would follow once it exists. Never add a leaf beyond the prints named here, and never weaken a statement to make it provable.

Deliverables: new files only, under ZInQKernel/Contrib/OneProof/RC/StageKummer/. Never import ZInQKernel.OneProof.Main, and edit nothing outside that directory except the report, .fleet/rc-stage-kummer.md and scratch/rc-stage-kummer/. Do not use local notation; write abbreviations with explicit arguments (the merge rule blocks local notation). Compile each file with lake env lean (one Lean process at a time), with no sorry and no axiom. Run #print axioms of each new theorem from a check file under scratch/rc-stage-kummer/, not in the deliverable files (only propext, Classical.choice and Quot.sound), and list the results in the report. The report docs/research/rc-stage-kummer.md needs:
- the main result, or the scoped stop, first;
- the statement of each new theorem, and which premise or field it supplies;
- the exact list of remaining hypotheses with their owners, and why each is strictly weaker than (O.7);
- a Known-issues section;
- a section "Manuscript check": one line per manuscript step you formalize or rely on, with its tex lines and one verdict: OK (right as written), gap filled (what was missing), error (what is wrong), or unverified (why).
Commit on your branch wip/rc-stage-kummer (only that branch) with the report (a background job pushes it; do not run git push), and give the final SHA in your last message and in .fleet/rc-stage-kummer.md.

Output and commits: besides the report, keep a results log at scratch/rc-stage-kummer/log.md (statements, findings, compile outcomes; no narrative), and at the end write .fleet/rc-stage-kummer.md (half a page: main result or scoped stop, what compiles, what remains). Commit as you go with git add of your own paths and git commit (never git add -A). Commit .fleet/rc-stage-kummer.md last. Resuming: if scratch/rc-stage-kummer/log.md exists, an earlier run was interrupted; read it and the report, and continue where it stopped. Keep working until .fleet/rc-stage-kummer.md is written and committed.
