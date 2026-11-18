rc-stages-ln: remove the `local notation` commands from ZInQKernel/Contrib/OneProof/RC/Stages/ with no statement change (base: wip/rc-stages at c653a7426f795b39762764fa31999a53c9e5922c).

Why: the merge scanner of the cloud agent that owns Theorem 5.3's reduction blocks `local notation` (fork issue #83, comment 6974088651), so this work cannot be merged until they are gone. rc-stages has one: ZInQKernel/Contrib/OneProof/RC/Stages/ExactGenus.lean:21, `local notation "H" => ringClassField (conductorOrder K c)`.

Setup: your worktree is already on branch wip/rc-stages-ln at c653a7426f795b39762764fa31999a53c9e5922c. Origin refs in the shared repository are refreshed for you; do not run git fetch or git push yourself (a separate job pushes your commits). Touch only files under ZInQKernel/Contrib/OneProof/RC/Stages/.

Your work:
1. Before editing, write scratch/rc-stages-ln/Check.lean: it imports each module you will change and runs `#check @name` for every theorem and definition declared in those files, under `set_option pp.notation false` and `set_option pp.explicit true`. Run it on the unchanged branch and save the output as scratch/rc-stages-ln/check-before.txt.
2. Replace every `local notation` command. In every theorem or definition statement, inline the notation's expansion at each use, so the elaborated statements stay exactly the same. Inside proofs you may instead use `let`/`set`, or a private abbreviation that takes every variable it mentions as an explicit argument (no section variables captured implicitly). Change nothing else: no statement, name, binder or proof strategy, beyond what the replacement needs. If you find other local syntax (`local infix`, `local macro`, `scoped notation`, `notation3`), list it in the report and leave it unchanged.
3. Rebuild the changed modules (lake env lean, one Lean process at a time), rerun scratch/rc-stages-ln/Check.lean, save scratch/rc-stages-ln/check-after.txt, and diff the two files. They must be identical, apart from source positions if any are printed; any other difference means a statement changed, so fix it. Rerun `#print axioms` for every theorem whose file changed: only propext, Classical.choice and Quot.sound.
4. Confirm with git grep that no `local notation` remains under ZInQKernel/Contrib/OneProof/RC/Stages/.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll.

Hygiene, for everything bound for the fork (Lean, report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the reviewer", "the cloud agent").

Deliverables: commits on your branch wip/rc-stages-ln only (a background job pushes them; never git add -A; git add your own paths). A short report docs/research/rc-stages-ln.md: the notations replaced (file, line, expansion, inlined or abbreviated), the check-before/check-after diff result, the compile and axiom results, and any other local syntax found. A results log at scratch/rc-stages-ln/log.md. At the end write .fleet/rc-stages-ln.md (a few lines: done or not, the final SHA, the diff result) and commit it last. Resuming: if scratch/rc-stages-ln/log.md exists, an earlier run was interrupted; read it and continue. Keep working until .fleet/rc-stages-ln.md is written and committed.
