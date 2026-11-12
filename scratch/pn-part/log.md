# pn-part log

Task: prove `matching` and `lemmaN1_core` in scratch/pn-design/PropN.lean (prefix `part_`).

## Setup
- `lake build ZInQKernel.Hypotheses.CR3Literature` (the `z_in_q` dependency was not built in this
  worktree): success.

## Step 1: generic partition sets (scratch/pn-part/Infra.lean)
- `part_IsP s Q` (blocks pairwise disjoint, sup = s, ∅ ∉ Q), `part_PS s` (finset of block sets),
  `part_mem_PS`, `part_sup_sdiff`, `part_IsP_sdiff`, `part_IsP_subset`, `part_toFP`,
  `part_sum_fp : ∑ P : Finpartition s, G P.parts = ∑ Q ∈ part_PS s, G Q`,
  `part_sum_subtype` (transport from `Finset t` to `Finset α` by `map (Embedding.subtype _)`).
- Compile: OK (no errors).
