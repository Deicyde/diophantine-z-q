# pn-part report

**Proved** in `scratch/pn-design/PropN.lean`, with no `sorry`: `matching` and `lemmaN1_core`.
No statement was changed; the only removed lines in the diff are the two `sorry`s. All 62 new
declarations (and the three sections) are named `part_…`. The shared infrastructure sits directly
above `lemmaN1_core`, and the matching-specific helpers directly above `matching`.
`#print axioms` (run on the scratch copy, `scratch/pn-part/Infra.lean`) gives only
`[propext, Classical.choice, Quot.sound]` for both theorems.

**Final compile** (`lake env lean scratch/pn-design/PropN.lean`): no errors and no other warnings.
```
scratch/pn-design/PropN.lean:864:8: warning: declaration uses `sorry`   -- lemmaN2
scratch/pn-design/PropN.lean:873:8: warning: declaration uses `sorry`   -- finalStep
```

**Size.** The file gains about 890 lines: about 300 of shared infrastructure, 400 for N1 and 190
for matching.

**Route** (pn-design §6, C and D):
- Partition sums are moved to "block sets" `Q : Finset (Finset ℕ)`, where `part_PS s` is the
  finset of block sets of set partitions of `s`. `part_sum_fp` passes from `Finpartition` to
  block sets, and `part_sum_subtype` from subtype blocks to ℕ blocks. This gives
  `part_Lam_eq : Lam m = part_LamS m.primeFactors`, `part_T5a_eq` and `part_T5b_eq`.
- Mod-8 bookkeeping: `part_prod_IsP` (the product over a partition), `part_pow3` (the product
  of blocks ≡ 1, 3 is 3^{#3}), and `part_adm_one` / `part_adm_three` (a Λ-admissible partition
  of a set of class 1, resp. 3, has no class-3 block, resp. exactly one).
- Reindexing `e ↦ e.primeFactors` for squarefree `n` (`part_sum_divisors`), with
  `(n/e).primeFactors = s \ B` (`part_Lam_div`).
- **matching**: the split lemma `part_split`, a bijection between partitions with exactly one
  block in a class `C` and pairs `(B, R)`, where `R` partitions `s \ B` and has no block in `C`.
  It is applied at the class-5 block (T5a) and at the class-7 block (T5b).
- **lemmaN1_core**: the product lemma `part_prod_lemma`, a bijection
  `(A, Q₁, Q₂) ↦ (Q₁ ∪ Q₂, Q₁)` onto pairs `(π, S ⊆ π)`. The subset counts mod 2 are
  `2^{#class-1 blocks}` for `m ≡ 3` (`part_inner3`) and `2^{b−1}` for `m ≡ 1` (`part_inner1`),
  so only `π = {s}` survives, with weight `g(m)`. For `m ≡ 1`, the representatives `d² < m` are
  first replaced by `p₀ ∣ d` for a fixed prime `p₀ ∣ m` (`part_sum_halves`, using the involution
  `d ↦ m/d`).

**Statement problems:** none. Both statements are true as stated.

**Note.** The worktree had no build of the `z_in_q` dependency (`lean/`), so I ran
`lake build ZInQKernel.Hypotheses.CR3Literature` once (Mathlib was not rebuilt).
