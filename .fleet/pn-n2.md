# pn-n2: `lemmaN2` proved

**Proved.** `ZInQ.PropN.lemmaN2` in `scratch/pn-design/PropN.lean` has no `sorry` (axioms:
propext, Classical.choice, Quot.sound). Its statement is unchanged, and so is every other
statement and proof in the file. The diff deletes one line (the `sorry`) and adds 279: 253 lines
of `n2_` helpers directly above `lemmaN2`, and a 22-line proof. The proof uses only `recursion`,
`eps_53`, `eps_pm1`, `L 1 = 1` and `Squarefree n`, as pn-design §4 says.

**Final compile** (`lake env lean scratch/pn-design/PropN.lean`, exit 0). The only warnings
besides the module-system notes are the other agents' sorries:
```
scratch/pn-design/PropN.lean:154:8: warning: declaration uses `sorry`   -- lemmaN1_core
scratch/pn-design/PropN.lean:455:8: warning: declaration uses `sorry`   -- finalStep
scratch/pn-design/PropN.lean:466:8: warning: declaration uses `sorry`   -- matching
```

**Route** (pn-design §6.B, the inductive identity):
- `n2_c ε L e d` is the coefficient of `Z(e)` in `P(d)`, defined by well-founded recursion that
  mirrors I1. `n2_P_eq` proves `P d = Σ_{e ∣ n, e ≡ 5,7} n2_c e d • Z e` by strong induction.
  The index set is fixed, so the sum swap is a plain `Finset.sum_comm`.
- `n2_c_mod` works in `ℤ[i]/(2)` and proves, by strong induction,
  `π(c_d(e)) = [e ∣ d] φ(d, e) L(d/e)`. In the case `e ∣ d`, `e ≠ d`, the term `q = m = d/e` is
  split off and the rest cancels by `Finset.sum_involution` with `q ↦ m/q`. There are no fixed
  points because `n` is squarefree.
- The residue facts are finite checks: `n2_kappa` (`κ(q) = κ(m/q)`), `n2_last`
  (`ε(e, m) ≡ φ(d, e)`) and `n2_eps`. `n2_eps` uses `−i ≡ i (mod 2)`, which is where the uniform
  `(5, 3)` class from `eps_53` comes in.
- Taking `d = n` gives `φ = 1`. Writing `c_n(e) = L(n/e) + 2w_e` gives `X = Σ w_e • Z e`.

**Statement problems:** none. The statement is true and was proved as stated.

**Build note:** this worktree had no build of the `lean/` (z_in_q) dependency, so
`lake env lean` at first failed with "unknown module prefix 'ZInQ'".
`lake build ZInQKernel.Hypotheses.CR3Literature` fixed this in about 3 minutes, with no
Mathlib rebuild.

Files: `scratch/pn-n2/N2.lean` (standalone development copy), `scratch/pn-n2/log.md`.
