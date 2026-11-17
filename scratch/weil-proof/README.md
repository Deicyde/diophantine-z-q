# scratch/weil-proof

Task weil-proof (docs/research/weil-proof.md). The theorems live in
`ZInQKernel/Contrib/OneProof/WeilFormula.lean` and `ZInQKernel/Contrib/OneProof/WeilFormulaTheta.lean`;
the files here are development copies and checks.

| file | content |
|---|---|
| `Generic.lean` | formula calculus, §20 parts (i)-(iv) (development copy of the first half of WeilFormula.lean) |
| `PBM.lean`, `Mates.lean` | `PullbackCompMonoidal` and the mates lemma (development copies) |
| `Theta.lean`, `Alt.lean`, `Div.lean` | §23: theta calculus, `alt_core`, divisibility (development copies) |
| `Axioms.lean` | `#print axioms` of the main theorems |
| `Discharges.lean`, `discharges.txt` | `#discharges` run and its output |
| `autofold.json` | **the spec** (nondegeneracy flagged pending reading): 34/11 -> 37/11 |
| `autofold-unread.json` | the same with pic-dict's "unread" flag: 34/11 -> 38/10 |
| `autofold-lf32.json` | spec for leaf-fold32b (phiAmpleIsogeny already folded): 16/21 -> 18/21; `FoldDryRunLF32.lean` compiled there |
| `FoldDryRun.lean`, `FoldDryRunUnread.lean` | dry-run modules (line 1 stripped), compile |
| `Test*.lean` | throwaway experiments |
| `log.md` | results log |
