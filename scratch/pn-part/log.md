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

## Step 2: matching (scratch/pn-part/Infra.lean, then PropN.lean)
- Block-set level (ℕ): `part_wt`, `part_LamAdm`, `part_LamS`, `part_T5aAdm`, `part_T5bAdm`;
  transports `part_Lam_eq : Lam m = part_LamS m.primeFactors`, `part_T5a_eq`, `part_T5b_eq`
  (via `part_transport`, `part_sum_fp`, `part_sum_subtype`).
- Mod 8: `part_prod_IsP` (product over a partition), `part_pow3`, `part_adm_one`,
  `part_adm_three`, `part_mod_sdiff`.
- Reindexing `part_sum_divisors` (e ↦ e.primeFactors, squarefree n), `part_Lam_div`.
- Split lemma `part_split`: partitions with exactly one block in `C` ↔ (B, R) with `C B`,
  `R` a partition of `s \ B` with no block in `C` (bijection (B, R) ↦ insert B R).
- `part_matching5a`, `part_matching5b`; `matching := ⟨part_matching5a hn hsq, part_matching5b hn hsq⟩`.
- Layout in PropN.lean: shared infrastructure directly above `lemmaN1_core`; matching helpers
  directly above `matching`. No other line changed (diff has no removed lines except the
  `sorry` of `matching`).
- `lake env lean scratch/pn-design/PropN.lean`: no errors; `declaration uses sorry` at
  lemmaN1_core, lemmaN2, finalStep (3 left).
