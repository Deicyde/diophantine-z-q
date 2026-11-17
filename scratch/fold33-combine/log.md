# fold33-combine log

Base: wip/leaf-fold33b 0e3c3125 (TailZ48, `sixContactMin_of_open41`; 33 H, strictest 13/20). origin/main c1e4ed1b is
already an ancestor of the base (no merge of main needed).

0. Merged origin/wip/sga3-nbhd (ac9ad381) and origin/wip/goodmodel-iso (894fb85b; it carries group-law, group-law-dvr
   and neron-ext). Clean merges. Scratch files that redeclare HDec.HSyn bundle structures renamed `.lean.txt`
   (content unchanged): scratch/sga3-nbhd/fold/TailZ46.lean (declares `HDec.HSyn.OpenResearchLeaves29` and
   `sixContactMin_of_open39`, which the base already has), scratch/sga3-nbhd/fold/FoldCheck.lean,
   scratch/neron-ext/AutofoldDry.lean (declares `OpenTextbookLeaves13`). Host paths in the merged logs, patches and
   overlay scripts replaced (worktree names; `cd "$(git rev-parse --show-toplevel)"` in the scripts).
   wip/charpoly-charp is not merged (see step 1).
