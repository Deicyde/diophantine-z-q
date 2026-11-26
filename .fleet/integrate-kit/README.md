# Landing kit

Scripts the landing lead runs from `~/dzq-runs/` (copy them there).

- `chain.sh N REF`: full landing chain for `origin/REF` in a clean checkout `~/dzq-check2`; writes `~/dzq-runs/wN-done`
  (one `KEY-EXIT=` line per autoland key, the `head <8 hex> ` line, axcheck's line and frozenTarget's axioms).
  One Lean job at a time; `MEMMAX` (default 60G) per job; 4 threads and CPUQuota=1600% when another Lean job runs
  on the host, else 16. `EXTRA_LEAN="a.lean b.lean"` runs extra files (exit 0, no error, standard axioms) and folds
  them into `CHECK-EXIT`. Run it from a tmux window: git fetch/push work there.
- `autoland-loop.sh`: every 2 minutes lands the newest line of `land-request.txt` if a matching `wN-done` passes
  every stage, by fast-forward or a docs-only merge of main; records `LANDED`/`SKIPPED` in `landed.txt`.
- `net.sh CMD...`: runs a git network command in a fresh tmux window and prints its output.
- `axcheck.py`, `site.sh`: helpers (axcheck reads the chain's `axioms-wN.txt`).

Seed `~/dzq-check2` with `git worktree add --detach ~/dzq-check2 origin/main` and a reflink copy of a built
`.lake` and `lean/.lake`.
