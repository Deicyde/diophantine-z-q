# eichler-rebase log

## Setup
* Merged origin/main c0f3d085 into wip/eichler-bound 09896d1f: no conflicts (commit 261ebb16). VERIFIED.
* Modules main lacks (git diff origin/main HEAD -- ZInQKernel): R5fpCountLe.lean, EichlerBound/{Order,Quadratic,Defs,
  Embed,Unit,Crit,Key,Key6,Inv,Count,Bound}.lean, GR56Lattice.lean (gr56-prove), GRDict.lean (gr-dict; not imported
  by R5fpCountLe). VERIFIED.
* Build tree seeded from ~/dzq-v-hfx-proof (TailZ42 base) by reflink copy; lake rebuilds the rest.

## Count (step 4)
* `autofold.py scratch/eichler-rebase/autofold.json --dry-run` (count-only spec, no new leaf) on main's kinds.tsv:
  `strict count: 11/18 on 29 -> 11/17 on 28; strictest 11/18 -> 11/17`. VERIFIED (autofold-dryrun.txt). The
  dry-run module itself is not a fold (dummy proof text): the field is removed by the bypass, not filled.
