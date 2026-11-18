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
| Appendices E and F pieces (#83) | project | `ZInQKernel/Contrib/OneProof/RC/AppE/` and `ZInQKernel/Contrib/OneProof/RC/AppF/` | none of their own; they feed `hRC` | the Theorem 5.3 lane's integration branch | Their statements land on that integration branch. |
