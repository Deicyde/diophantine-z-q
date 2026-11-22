ccl-retire2: finish the Cai–Chen–Liu retirement on current main: build the whole tree, write the report, and say what count it lowers (base: wip/ccl-retire at f23ac367e6f18dbae33b8f75ec66a7ba4e868927, with main 2ba691fde6bfb9e514a429414ba92a6c6893a63f merged in).

Why: the earlier run (wip/ccl-retire) applied the retirement plan from docs/research/ccl-unit-index2.md, "Retirement at fold". It deleted CommonCoordinate18LeafE2.lean, CommonCoordinate18E2.lean and H20HeegnerNorm.lean, added Wiring/ChainCond.lean, respelled the four premises as the existential anchored NormRelations, and deleted CCLThm2_15Applied. Its scratch/ccl-retire/builds.txt records PASS for the changed modules and their importers, and staged axiom checks on 20 declarations. It stopped before the builds of ZInQKernel.OneProof.Main and ZInQKernel.OneProof.Discharges, and it wrote no docs/research/ccl-retire.md and no .fleet/ccl-retire.md. Its base batch has since landed on main without it, so this run brings it onto current main and finishes it.
Do not overlap: the RC lanes for hcm, the O.7 integral model and the even inventory. Change no statement beyond what the retirement plan names.

Setup: git fetch origin wip/ccl-retire main. Create branch wip/ccl-retire2 at f23ac367e6f18dbae33b8f75ec66a7ba4e868927. Then git merge --no-edit 2ba691fde6bfb9e514a429414ba92a6c6893a63f (checked: merges cleanly).

What exists (read first): docs/research/ccl-unit-index2.md ("Retirement at fold"); scratch/ccl-retire/ (log.md, builds.txt, Check.lean, axioms.txt); the three commits on wip/ccl-retire after a59ea33fe90ba2b0aa39f896137097180aad5f6e.

Your work:
1. Consumer search on the merged base, in scratch/ccl-retire2/log.md. Main has gained modules since the earlier base. git grep for every declaration and module the retirement deleted (CCLThm2_15Applied, the declarations of the three deleted files, hnorm_of_print_on, CCLGenuine, hnorm_of_genuine_print), and for imports of the deleted modules. If a new reference exists, stop for that declaration and report it, rather than widening the deletion.
2. Build, one target at a time: ZInQKernel.OneProof.Main, ZInQKernel.OneProof.Discharges, ZInQKernel.Contrib.OneProof.RC.Wiring.ChainCond, and every module that imports a changed or deleted module on the merged base (list them with git grep). Record each result in scratch/ccl-retire2/builds.txt. Rerun scratch/ccl-retire/Check.lean, adding #print axioms for ZInQ.OneProof.frozenTarget if it is not there, and save the output as scratch/ccl-retire2/axioms.txt.
3. Count: say exactly what the retirement lowers. Name the field of ZInQ.OneProof.frozenTarget it removes, or the GLUE or LEAF rows of docs/one-proof/kinds.tsv or OPEN.md it changes, with file:line on main. If the deleted declarations are outside the closure of frozenTarget and hRC, so that no field or count changes, say "none" plainly and give the closure evidence (scratch/ccl-unit-index2/closure.py or its equivalent rerun on this base). Do not edit kinds.tsv, claims.tsv, OPEN.md or Main.lean; those are the integrator's.
4. Write docs/research/ccl-retire.md: the result first; each deleted declaration and file; each respelled premise; the build list with results; the count answer from step 3; Known issues. Write .fleet/ccl-retire2.md, a short summary.
Stop rule, for this unattended run: if a build fails because of the retirement, restore only the deletion that caused it, record the dependency, and continue with the rest. Never weaken a statement.
Out of scope: new mathematics, any change to the weighted print CCLThm2_15AppliedWithUnits or to the staged statements.
Prints: none.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll. Run Lean under MemoryMax 60G. Run one lake command at a time, never two in parallel, and never a check while a build runs.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Add no print. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/ccl-retire2.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer").

Deliverables: the merged branch with the retirement intact; scratch/ccl-retire2/ (log, builds.txt, axioms.txt); docs/research/ccl-retire.md; .fleet/ccl-retire2.md. No sorry and no axiom; only propext, Classical.choice and Quot.sound in the axiom output.
Commit as you go (after each step that compiles). Commit and push your branch wip/ccl-retire2 (only that branch) with the report; give the final SHA in your last message.

Build note (read before compiling): the worktree's .lake was copied from a build of the fork's main, so modules that exist only on your base branch (or arrive with your merge) have no .olean yet, and lake env lean on a file that imports them stops with a missing-object error. Before checking your own files, build their imports once with lake build <Module> for each module your files import (one Lean process at a time; let each finish), then compile your files. Never report a file as unchecked because an import was not built: build it. Report any file that still fails, with the error. One Lean process at a time means one lake command at a time: let each lake build or lake env lean finish before starting the next, never run two in parallel, and never start a check while a build is running.
