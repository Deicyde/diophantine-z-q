# eichler-rebase log

## Setup
* Merged origin/main c0f3d085 into wip/eichler-bound 09896d1f: no conflicts (commit 261ebb16). VERIFIED.
* Modules main lacks (git diff origin/main HEAD -- ZInQKernel): R5fpCountLe.lean, EichlerBound/{Order,Quadratic,Defs,
  Embed,Unit,Crit,Key,Key6,Inv,Count,Bound}.lean, GR56Lattice.lean (gr56-prove), GRDict.lean (gr-dict; not imported
  by R5fpCountLe). VERIFIED.
* Build tree seeded from ~/dzq-v-hfx-proof (TailZ42 base) by reflink copy; lake rebuilds the rest.
