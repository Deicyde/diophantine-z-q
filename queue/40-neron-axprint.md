neron-axprint: settle by #print axioms whether NeronExt.NeronDVRLocal is proved on main or is an uncounted leaf (base: main at 29bfbc3f6793d98b7c1ac637f9728fe51e701e5b). Report only.

Why: the reviewer calls NeronDVRLocal (ZInQKernel/Contrib/OneProof/NeronSchemeExtensionExists.lean:390, docstring "LEAF; published", BLR §1.4 Thm. 3) an uncounted leaf. The O.7 Néron lane (RC/ModelNeron/LocalExtension.lean:24, RC/ModelNeron/LocalTarget.lean:67) takes it as a hypothesis. Main also has a proof chain nearby: NeronDVR.neronSchemeExtensionDedekind_proof (NeronDVR/RelativeSquare.lean:83) proves NeronSchemeExtensionDedekind, and NeronExt.dvrLocal_of_extension (NeronSchemeExtensionExists.lean:421) derives NeronDVRLocal from ZInQ.Contrib.NeronC.NeronSchemeExtensionExists. A text search on main found no closed term of type NeronSchemeExtensionExists or NeronDVRLocal, only conditional theorems; the kernel has to confirm that.
Do not overlap: the O.7 lanes (rc-model-target, generic4, rc-model-neron) and the hcm lane. Change nothing in the library.

Setup: git fetch origin main. Create branch wip/neron-axprint at 29bfbc3f6793d98b7c1ac637f9728fe51e701e5b.

Your work:
1. Producers: git grep main for every declaration whose type is NeronDVRLocal, NeronSchemeExtensionExists or NeronSchemeExtensionDedekind, or which takes one of them and returns another (a bridge, e.g. Dedekind -> Exists or Dedekind -> DVRLocal). List each with file:line and its hypotheses in scratch/neron-axprint/log.md.
2. Write scratch/neron-axprint/Check.lean, which imports what it needs and contains #print axioms for NeronDVR.neronSchemeExtensionDedekind_proof, NeronExt.dvrLocal_of_extension, NeronExt.extension_of_dvrLocal and each producer from step 1. If step 1 finds a chain that should give NeronDVRLocal outright, add `example : NeronExt.NeronDVRLocal := <that chain>` so the kernel checks it. Build the imports first (build note), then run lake env lean on Check.lean, one Lean process at a time. Save the output as scratch/neron-axprint/axioms.txt.
3. Write docs/research/neron-axprint.md, verdict first: either "NeronDVRLocal is proved on main by <chain>, standard axioms", or "NeronDVRLocal has no closed proof on main; the nearest is <declaration>, missing <the exact bridge>". List where NeronDVRLocal is consumed on main (file:line) and whether any count file (docs/one-proof/kinds.tsv, OPEN.md) mentions it. Write .fleet/neron-axprint.md, a short summary.
Stop rule, for this unattended run: report only. Do not try to prove a missing bridge; name it and stop.
Out of scope: new mathematics, edits to any existing file, any count file.
Prints: none.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll. Run Lean under MemoryMax 60G. Run one lake command at a time, never two in parallel, and never a check while a build runs.

The owner's rules: follow the manuscript (diophantine_zq.tex) first, then the literature it cites. Add no print. Report any error you find in the manuscript or a source at once, first in the report and in .fleet/neron-axprint.md.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer").

Deliverables: branch wip/neron-axprint with scratch/neron-axprint/ (log.md, Check.lean, axioms.txt), docs/research/neron-axprint.md and .fleet/neron-axprint.md. No library file changes.
Commit as you go. Commit and push your branch wip/neron-axprint (only that branch) with the report; give the final SHA in your last message.

Build note (read before compiling): the worktree's .lake was copied from a build of the fork's main, so modules that exist only on your base branch (or arrive with your merge) have no .olean yet, and lake env lean on a file that imports them stops with a missing-object error. Before checking your own files, build their imports once with lake build <Module> for each module your files import (one Lean process at a time; let each finish), then compile your files. Never report a file as unchecked because an import was not built: build it. Report any file that still fails, with the error. One Lean process at a time means one lake command at a time: let each lake build or lake env lean finish before starting the next, never run two in parallel, and never start a check while a build is running.
