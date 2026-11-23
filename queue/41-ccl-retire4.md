ccl-retire4: rebuild the Cai–Chen–Liu retirement on current main after the review's docstring fixes, including the nine downstream modules not yet compiled, and refresh the build and axiom evidence (base: wip/ccl-retire3 at f5299bb9d6f9ada2fcd170099f784f0e0945bf79, which is wip/ccl-retire2 with current main 29bfbc3f6793d98b7c1ac637f9728fe51e701e5b merged in plus two docstring-only commits).

Why: the review of wip/ccl-retire2 found no blockers. It asked for four things before a draft PR: (1) docstrings that still named the retired declarations, or called the unweighted relation (4.1) the print, are fixed (done in the base commit; docstring-only); (2) the build and axiom evidence was produced on a merge with an older main (2ba691fde6bfb9e514a429414ba92a6c6893a63f), not with current main; (3) nine modules lost H20HeegnerNorm from their import closure and were never compiled; (4) report cites were pinned to the older main. This run produces the evidence on the tree the PR will merge into. It is a cleanup: no count change is expected.
Do not overlap: the RC lanes for hcm, the O.7 integral model and the even inventory. Change no statement.

Setup: git fetch origin wip/ccl-retire3. Create branch wip/ccl-retire4 at f5299bb9d6f9ada2fcd170099f784f0e0945bf79. The base already contains current main; do not merge anything else.

What exists (read first): docs/research/ccl-retire.md; scratch/ccl-retire2/ (log.md, builds.txt, axioms.txt); scratch/ccl-retire/Check.lean (the axiom check, which includes ZInQ.OneProof.frozenTarget); the two docstring-only commits on top of the merge (git log --stat -2).

Your work:
1. Build, one target at a time, recording each result in scratch/ccl-retire4/builds.txt: ZInQKernel.OneProof.Main, ZInQKernel.OneProof.Discharges, ZInQKernel.Contrib.OneProof.RC.Wiring.ChainCond, every target listed as PASS in scratch/ccl-retire2/builds.txt, every module changed against main (git diff --name-only 29bfbc3f6793d98b7c1ac637f9728fe51e701e5b HEAD -- '*.lean', excluding deleted files), and these nine modules, which lost H20HeegnerNorm from their import closure: ZInQKernel.Contrib.CloudB3E1RingClass.CalPointActual, ZInQKernel.Contrib.CloudB3E2Norm.CentralSpecC1, ZInQKernel.Contrib.CloudB3E2Norm.CentralSpecCone, ZInQKernel.Contrib.CloudB3E2Norm.CentralTwistDict, ZInQKernel.Contrib.CloudB3E2Norm.H20QuadFrob, ZInQKernel.Contrib.OneProof.RC.CMScope.Anchor, ZInQKernel.Contrib.OneProof.RC.HeegnerAnchor.AtScale, ZInQKernel.Contrib.OneProof.RC.Wiring.CommonCoordinate19DualS, ZInQKernel.Contrib.RC53Assist.CentralStageReduction.ReductionV3. Check each module name with git ls-files before building; if a name does not resolve, record it and find the module that matches the path.
2. Rerun scratch/ccl-retire/Check.lean on this tree and save the output as scratch/ccl-retire4/axioms.txt (only propext, Classical.choice and Quot.sound may appear).
3. Recompute the import closure of ZInQKernel.OneProof.Main and of the type of hRC on this tree (the method of scratch/ccl-retire2/log.md, section "Import closure and count") and confirm that neither contains a changed or deleted module.
4. Update docs/research/ccl-retire.md: the build and axiom links point at scratch/ccl-retire4/; the Count paragraph gives the module counts on this tree, with the commit; cite hRC by name with its line in ZInQKernel/OneProof/Main.lean on this tree. Write scratch/ccl-retire4/log.md (commands and results, no narrative) and .fleet/ccl-retire4.md, a short summary.
Stop rule, for this unattended run: if a build fails, record the failure with the first error, do not change any statement, and report it first; a failure caused by one of the two docstring-only commits may be fixed in a commit of its own (comment text only), named in the report.
Out of scope: new mathematics, any change to statements, to the weighted print CCLThm2_15AppliedWithUnits, or to kinds.tsv, claims.tsv, OPEN.md and Main.lean.
Prints: none.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll. Run Lean under MemoryMax 60G. Run one lake command at a time, never two in parallel, and never a check while a build runs.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Add no print. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/ccl-retire4.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer").

Deliverables: scratch/ccl-retire4/ (log.md, builds.txt, axioms.txt); the updated docs/research/ccl-retire.md; .fleet/ccl-retire4.md. No sorry and no axiom.
Commit as you go (after each step that compiles). Commit and push your branch wip/ccl-retire4 (only that branch) with the report; give the final SHA in your last message.

Build note (read before compiling): the worktree's .lake was copied from a build of the fork's main, so modules that exist only on your base branch (or arrive with your merge) have no .olean yet, and lake env lean on a file that imports them stops with a missing-object error. Before checking your own files, build their imports once with lake build <Module> for each module your files import (one Lean process at a time; let each finish), then compile your files. Never report a file as unchecked because an import was not built: build it. Report any file that still fails, with the error. One Lean process at a time means one lake command at a time: let each lake build or lake env lean finish before starting the next, never run two in parallel, and never start a check while a build is running.
