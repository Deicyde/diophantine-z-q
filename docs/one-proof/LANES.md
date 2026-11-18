# Lanes: parallel work without contention

A lane is one unit of project work: one issue (template "Lane"), one owner, one branch, and a declared footprint.

- **Footprint.** The issue lists the directories and files the lane writes and the board rows it changes. Two lanes
  run at the same time only if their footprints do not overlap. If they must overlap, one depends on the other.
- **New files, one directory.** New Lean goes in new files under the lane's own directory (outside contributors:
  `ZInQKernel/Contrib/OneProof/`). Existing modules change only in folds.
- **One writer per shared file.** [OWNERS.tsv](../../OWNERS.tsv) names the single writer of each shared or generated
  file. Generated files (OPEN.md, open-statements.json, pages-wanted.md) are written only by the folds. claims.tsv is
  written only by the claims sync. A change to someone else's file goes through its owner.
- **See what is coming.** [fold-queue.tsv](fold-queue.tsv) lists what is about to land, and
  `volatile.tsv` (in this directory, once the integrator first uses it) lists board rows that a queued fold will remove
  or rename: do not start work on those.
- **Before pushing.** Run `scripts/push_gate.sh`: it merges current `main` with your branch in memory, stops on
  conflicts, and checks that the merge does not drop board rows that `main` has.
- **Pull requests.** The PR guard runs the same row check. A pull request that removes rows on purpose lists them on a
  `Removes-rows:` line of its body. It also warns when the change touches files with an owner, and when the generated
  files are out of date.
- **Decisions** are recorded once, in [docs/DECISIONS.md](../DECISIONS.md), with a link to where they were made.

## Standing lanes

These lanes run continuously. A new lane checks its footprint against them, and each piece of work inside them is
still claimed in public (on #14 or #83) before it starts.

| Lane | Owner | Writes | Board rows | Depends on | Done when |
|---|---|---|---|---|---|
| Contributor agents working from #14 | project | One new file per claimed field under `ZInQKernel/Contrib/OneProof/`, named after the field. Statement checks are reported as comments on #14, with no files. | The one field each agent has claimed on #14. | A `Claiming <field> at <commit>` comment on #14 for a row that is `open` and not held. Never a row or lane of #83. | The fold shows the field discharged, or the check is recorded in reviews.tsv. |
| Theorem 5.3 (#83) | project | `ZInQKernel/Contrib/OneProof/RC/` and `ZInQKernel/Contrib/CloudB3RC53/` | `hPC` until #90 lands, then `hRC` | #90 | `hRC` rests only on printed results, through pull requests to `main`. |
| Appendix F piece: the Eichler order and its class set at one stage, tex 8462–8473, with the p-neighbours of 8476–8493 and 9039–9076 (branch `wip/rc-eichler`; [claim on #83](https://github.com/Deicyde/diophantine-z-q/issues/83#issuecomment-6968250894)) | project | `ZInQKernel/Contrib/OneProof/RC/Eichler/`, `docs/research/rc-eichler.md`, `scratch/rc-eichler/` | none of its own; it supplies the theta side of (O.7), fields of `Visibility.ThetaStage` and `AppF.ThetaStage`, to `hRC` | the Theorem 5.3 lane's integration branch `rc/thm53-proof-20261117` at `7c8dc74b` | The class set, its unit groups and the p-neighbours land on that integration branch with only the standard axioms, or a scoped report names what is missing and what to adjust in `ThetaSide`. |
