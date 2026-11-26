regen-gate-1: build and gate commit 1 (Berger restore) of the fold desk's regeneration branch fold/regen-1126, at 2ce6851a600876005f5cb44160445afe34fcc5d3 (your base). Check only: change no Lean, scripts or generated files of the branch.

Why: every change to frozenTarget's hypotheses goes through the copy chain one commit at a time. The lead and the fold desk need each commit gated at its own SHA before the chain lands it.

Setup: your worktree is on branch wip/regen-gate-1 at 2ce6851a600876005f5cb44160445afe34fcc5d3. Confirm with git rev-parse HEAD before anything else, and stop if it differs. Do not fetch, merge or rebase.

Gates, in order, one Lean process at a time (throttle line below):
1. Build ZInQKernel.OneProof.Main, then ZInQKernel.OneProof.Discharges (`lake build ZInQKernel.OneProof.Main`, then `lake build ZInQKernel.OneProof.Discharges`). Never let a single tool call run longer than 2 hours: the tool stops background jobs at 2 hours. If a build would run longer, build its imports one module at a time (`lake build <Module>`, each in its own call, one after another) and then resume the target; lake resumes incrementally. Record each command's result and wall time, and any error verbatim.
2. `#print axioms ZInQ.OneProof.frozenTarget` in scratch/regen-gate-1/Axioms.lean, run with lake env lean. Only propext, Classical.choice and Quot.sound may appear.
3. The frozen hypotheses: `#check @ZInQ.OneProof.frozenTarget` in the same file. Record the hypothesis count and list the field names of its bundles. Compare them with this commit's stated effect (OpenResearchLeaves78's colmezThm01 : PanBergerRefereed.ColmezThm01 is replaced by bergerSurveyF : PanDict.BergerSurveyF; hypothesis count 22) and say whether they match.
4. `lake env lean scripts/one_proof/OpenStatements.lean` (writes docs/one-proof/open-statements.json), then `python3 scripts/one_proof/render_open.py --check`. Expected: only "out of date" messages for the generated files. Any other message (row checks, unclassified hypotheses) is a failure: quote it.
5. While the regenerated JSON is still in the tree: `python3 -I scripts/one_proof/vault_chapter/gen.py`. Record its output verbatim (file count, removed or added chapter files, any "note:" line or assertion).
6. Restore every generated file with git checkout (docs/one-proof/, blueprint/, and anything else gates 4-5 touched), and confirm that git status shows only your scratch/regen-gate-1/ files and .fleet/regen-gate-1.md.

Report: .fleet/regen-gate-1.md, first lines: the SHA from rev-parse; then pass or fail for each gate; the axiom output; the hypothesis count and fields; the render_open and gen.py messages. scratch/regen-gate-1/log.md: a results log of commands, outcomes and wall times. Commit only those paths (git add of your own paths, never git add -A), give the final SHA in your last message, and stop. A background job pushes the branch.

Stop rule, for this unattended run: report only. Do not fix a failure. Record it with the error and the module, and finish the report.

RESOURCE LIMITS (hard rules; breaking one fails your task):
- At most ONE Lean process (lean, lake, repl, or a pytest run that starts real Lean) at a time. Never start Lean jobs in the background with &, xargs -P, or shards.
- A Lean REPL session gets at most 10 commands, then restart it. Or send the header once and pass "env" on later commands so it doesn't re-import.
- Check `uptime` and `sysctl vm.swapusage` before every Lean or pytest run. If load is above 40 or swap used is above 8 GB, don't start it; report that you were blocked.
- Ground-truth or differential checks use a sample of at most 30 inputs, run one after another.
Host note (devserver): check `uptime` and `free -g` instead of vm.swapusage; hold Lean only above load 120 or below 20 GB available memory; do not sleep and poll. Run Lean under MemoryMax 60G. Run one lake command at a time, never two in parallel, and never a check while a build runs.
Throttle (the lead, 11-21): run every Lean build as `LEAN_NUM_THREADS=4 systemd-run --user --scope -q -p CPUQuota=1600% -p MemoryMax=60G nice lake build ...`. Never touch other worktrees or their processes.

Hygiene, for everything bound for the fork (report, commit messages): no session names, host names or user paths. Write paths relative to the repository root, and refer to people by role ("the lead", "the fold desk").

Build note (read before compiling): the worktree's .lake was copied from a build of the fork's main, so modules that exist only on your base branch have no .olean yet. Build their imports with lake build before checking files, one Lean process at a time.
