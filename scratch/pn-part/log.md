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

## Step 3: lemmaN1_core (scratch/pn-part/Infra.lean, then PropN.lean)
- `part_PS_empty`, `part_LamS_empty`, `part_Lam_one : Lam 1 = 1`.
- Product lemma `part_prod_lemma`: Σ_{A ⊆ s} Σ_{Q₁ ∈ PS A} Σ_{Q₂ ∈ PS (s∖A)} F Q₁ Q₂ =
  Σ_{π ∈ PS s} Σ_{S ⊆ π} F S (π ∖ S) (bijection (A, Q₁, Q₂) ↦ (Q₁ ∪ Q₂, Q₁)).
- `part_expand`: Σ_{A ⊆ s, P A} Λ(A)Λ(s∖A) as the triple sum.
- Counts mod 2: `part_two_pow_smul` (2^k • c = [k = 0] c), `part_count_subset`
  (Σ_{S ⊆ π} [S ⊆ X] c = [X = ∅] c), `part_count_mem` (Σ_{S ⊆ π} [B₀ ∈ S] c = [|π| = 1] c).
- `part_inner3` (m ≡ 3: S ⊆ class-1 blocks, count 2^{#class-1}), `part_inner1` (m ≡ 1: all
  blocks class 1, S ∋ block of p₀, count 2^{b−1}); only π = {s} survives (`part_eq_single`).
- `part_sum_halves`: representatives `d² < m` replaced by `p₀ ∈ d.primeFactors` (involution
  d ↦ m/d, symmetric summand).
- `part_N1_three`, `part_N1_one`; `lemmaN1_core := ⟨part_Lam_one, part_N1_one, part_N1_three⟩`.
- Replaced deprecated `if_pos/if_neg/dif_neg/if_true` by `ite_eq_left/ite_eq_right/
  dite_eq_right/ite_true` (same signatures) in my code.
- `#print axioms` (on the scratch copy): matching, lemmaN1_core depend on
  [propext, Classical.choice, Quot.sound].
- `lake env lean scratch/pn-design/PropN.lean`: no errors, no other warnings; output:
  `PropN.lean:864:8: warning: declaration uses 'sorry'` (lemmaN2),
  `PropN.lean:873:8: warning: declaration uses 'sorry'` (finalStep).
