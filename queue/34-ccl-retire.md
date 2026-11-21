ccl-retire: retire the older unweighted Cai–Chen–Liu transport, following the plan in docs/research/ccl-unit-index2.md, section "Retirement at fold" (base: wip/rc-lane-batch-1121a at a59ea33fe90ba2b0aa39f896137097180aad5f6e).

Why: ccl-unit-index2 found that Cai–Chen–Liu, Trans. AMS 370 (2018), Theorem 2.15, p. 3730, weights the relative trace by u_m, with u_1 = [𝒪_K^× : ℤ^×]. The older applied witness CCLThm2_15Applied omits this factor, although its premises allow discriminant −4. The staged chain now uses CCLThm2_15AppliedWithUnits and proves the factor is one in the manuscript's application. The older transport lies outside the import closures of hRC and ZInQ.OneProof.frozenTarget, but it still states the unweighted witness as if printed. The lead asked that it be retired at fold, so that the tree no longer carries a statement stronger than the print. The project claims it on fork issue #83.
Do not overlap: the RC lanes for the even inventory, hcm, and the O.7 integral model. Change nothing in the staged chain beyond what the retirement plan names.

Setup: git fetch origin wip/rc-lane-batch-1121a. Create branch wip/ccl-retire at a59ea33fe90ba2b0aa39f896137097180aad5f6e. This task edits and deletes existing files, as listed below; there is no new directory.

What exists (read first):
- docs/research/ccl-unit-index2.md: the whole report, especially "Retirement at fold", and scratch/ccl-unit-index2/ (closure.py, closure.txt, consumer-refs.txt, builds.txt).
- ZInQKernel/Contrib/OneProof/RC/PrintsArith/Heegner.lean: CCLThm2_15Applied (old) and CCLThm2_15AppliedWithUnits (new); ZInQKernel/Contrib/OneProof/RC/CCLUnitIndex/Units.lean.
- The files the plan names: OneProof/RC/Wiring/CommonCoordinate18LeafE2.lean, OneProof/RC/Wiring/CommonCoordinate18E2.lean, CloudB3E2Norm/H20HeegnerNorm.lean, H20Transport.lean, H20Anchor.lean, H20DictFields.lean, H20PresClass.lean, H20PresClassOf.lean, H20PresClassMatch.lean (paths relative to ZInQKernel/Contrib/).

Your work:
1. First, in scratch/ccl-retire/log.md: rerun the consumer search on this base with git grep for every declaration the plan deletes. The base now includes current main, so new importers may exist. Record each reference. If a reference outside the plan's list exists, stop for that declaration and report it, rather than widening the deletion.
2. Carry out the plan exactly:
   - Delete CommonCoordinate18LeafE2.lean and its declarations.
   - Move chainCond and dvd_chainCond into a new module, point the staged import at it, then delete CommonCoordinate18E2.lean.
   - Delete H20HeegnerNorm.lean. In H20Transport.lean, import PrintsArith.Heegner directly and delete hnorm_of_print_on.
   - In H20Anchor.lean, delete CCLGenuine and hnorm_of_genuine_print, and keep the subgroup and full-anchor dictionaries.
   - Respell the premise of H20DictFields.hnorm_of_full_anchor, H20PresClass.gx_step_anchored, H20PresClassOf.gx_step_heegner and H20PresClassMatch.gx_step_heegner_at as the existential anchored NormRelations.
   - Delete CCLThm2_15Applied.
   - Keep HeegnerPointData.NormRelations.
3. Remove every import of a deleted module, including in ZInQKernel/Contrib/ALLCONTRIB.lean or any aggregate import file if one lists them.
4. Build: lake build ZInQKernel.OneProof.Main, ZInQKernel.OneProof.Discharges, and every module that imported a changed or deleted module on the base (use scratch/ccl-unit-index2/closure.py or git grep to list them). Build one at a time. Run #print axioms from scratch/ccl-retire/Check.lean on the staged chain's main declarations (the theorems scratch/ccl-unit-index2/Check.lean checks) and on frozenTarget.
5. Stop rule: if a deletion breaks a module the plan does not name, restore that deletion, record the dependency, and continue with the rest.
Out of scope: any change to the staged statements or the weighted print; new mathematics.
Prints: none; this run removes one unweighted applied witness.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll. Run Lean under MemoryMax 60G. Run one lake command at a time, never two in parallel, and never a check while a build runs.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Add no print. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/ccl-retire.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer").

The stop rule, for this unattended run: if a step cannot be done as the plan states, do the rest, and write a scoped report saying what was left and why. Never weaken a statement.

Deliverables: the edits and deletions above, a new module for chainCond, scratch/ccl-retire/ (log, Check.lean, axioms output, list of builds with results), docs/research/ccl-retire.md (the result first, each deleted declaration and file, each respelled premise, the build list, and a Known-issues section) and .fleet/ccl-retire.md. Do not use local notation. Compile with no sorry and no axiom; only propext, Classical.choice and Quot.sound in the axiom output.
Commit as you go (after each step that compiles). Commit and push your branch wip/ccl-retire (only that branch) with the report; give the final SHA in your last message.

Build note (read before compiling): the worktree's .lake was copied from a build of the fork's main, so modules that exist only on your base branch (or arrive with your merge) have no .olean yet, and lake env lean on a file that imports them stops with a missing-object error. Before checking your own files, build their imports once with lake build <Module> for each module your files import (one Lean process at a time; let each finish), then compile your files. Never report a file as unchecked because an import was not built: build it. Report any file that still fails, with the error. One Lean process at a time means one lake command at a time: let each lake build or lake env lean finish before starting the next, never run two in parallel, and never start a check while a build is running.
