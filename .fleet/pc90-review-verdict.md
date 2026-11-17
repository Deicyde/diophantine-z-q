# pc90-review: ERROR found (early notice)

PR #90 head 517e05cce is NOT clean to land as is.

1. Retained source committed. `scratch/upstream/parity-frozen-4eaee875.tex` (Elliot's supplement S12, 718 lines,
   32153 bytes) is tracked in the PR tree. It was added by commit 4b2595108, whose message says the opposite
   ("untrack the empty scratch placeholder (the S12 copy stays local and uncommitted)"); 631a68420 had added an empty
   placeholder. S12 is retained source and must not be committed or redistributed. Fix: `git rm --cached` it in a new
   commit and, since the file is in the PR history, squash or rewrite before merging into a public branch.

2. Base: the PR is not on fork main 5f1fac79; its merge base with 5f1fac79 is 67950e82 (5f1fac79 adds PRs #87-#89).
   `git merge-tree` of HEAD with 5f1fac79 is conflict-free, so this is a note, not a blocker.

Review continues; full report in docs/research/pc90-review.md.
