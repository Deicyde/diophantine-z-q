# jp-compile: draft fork PR #38 proves `hJP`

## Verdict

**PR #38 (base a9bc2e35, branch work/h10-jones-pall-40944c0a) proves the top hypothesis
`hJP : ZInQ.Contrib.TYZDecomp.H29Split.JonesPallX2Y2Z16` on this toolchain, unchanged and with no new leaves.**
VERIFIED (compiled on Lean 4.35.0, Mathlib v4.35.0, 2026-11-16, with origin/main 0caafe66 merged):

* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.JonesPall`
  succeeds (13704 jobs). The PR's six modules build in about 100 s together. The only warnings are Mathlib's
  notices that its modules are "designed for use with the module system". **No technical fix was needed. This task
  changed no file under `ZInQKernel/`.**
* `#discharges` (`scratch/jp-compile/Discharges.lean`, output `Discharges-output.txt`):

  ```
  DISCHARGES [hJP] by ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof
    still assumes: []
    axioms: [propext, Classical.choice, Quot.sound]
  #discharges: 56 open hypotheses, 3047 theorems checked, 8 discharge one
  ```

  The other seven DISCHARGES lines come from contributions already folded on main and are unrelated.
* The theorem's type matches the binder: a MetaM check over `frozenTarget`'s binders finds `hJP` with type
  `ZInQ.Contrib.TYZDecomp.H29Split.JonesPallX2Y2Z16`, syntactically equal (`==`) and definitionally equal to
  `jonesPall_proof`'s type. The application `frozenTarget r t l g (hJP := jonesPall_proof)` elaborates.
* `#print axioms`: `jonesPall_proof` and `jonesPall_representation` depend on `[propext, Classical.choice,
  Quot.sound]` only. `Lean.ofReduceBool` does not appear, so no `native_decide` is used anywhere in the closure.
* Manual fold check (`scratch/jp-compile/FoldCheck.lean`, output `FoldCheck-output.txt`). The file is main's
  `ZInQKernel/OneProof/Main.lean` body with the binder `(hJP : H29Split.JonesPallX2Y2Z16)` dropped and
  `ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof` passed to `tyzLemma29Mod2_of_sixLeaves` in its place, plus
  `import ZInQKernel.Contrib.OneProof.JonesPall`. It compiles. `frozenTarget` depends on the standard axioms only,
  and `#check` shows the signature without `JonesPallX2Y2Z16`. **Result: hJP removed, one fewer top hypothesis
  (56 to 55).**

## The proof (summary; the kernel has checked it)

The proof is `jonesPall_representation` in `ZInQKernel/Contrib/OneProof/JonesPall/Representation.lean`. Take
`n` squarefree with `n ≡ 1 (mod 8)`.

1. If no prime factor of `n` is `≡ 3 (mod 4)`, Mathlib's two-square criterion
   (`ZMod.isSquare_neg_one_iff_forall_mem_primeFactors_mod_four_ne_three` and
   `Nat.eq_sq_add_sq_of_isSquare_mod_neg_one`) gives `n = x² + y²`, so `z = 0`.
2. Otherwise fix a prime `p | n` with `p ≡ 3 (mod 4)`.
3. Legendre's theorem (the ported atlas-lean proof) gives `n = a² + b² + c²`. Mod 8 there are two patterns: `a`
   odd with `b ≡ c ≡ 0 (mod 4)`, which is done, or `a` odd with `b ≡ c ≡ 2 (mod 4)`.
4. In the second case, let `v = ai + bj + ck`, so `v² = -n ≡ 0 (mod p)`. Since `n` is squarefree, `v ≢ 0 (mod p)`.
   A Lagrange–Euler descent, adapted from Mathlib's `SumFourSquares`, gives an integral quaternion `q` with
   `N(q) = p` and `qv ≡ 0 (mod p)` (`exists_norm_prime_annihilator`).
5. Then `w = q v q̄ / p` is a pure quaternion of norm `n`. Conjugating by a quaternion of norm `≡ 3 (mod 4)` takes
   the bad pattern to one with `4 | j` and `4 | k` (`conjugation_bad_pattern`, a residue table checked by kernel
   `decide`). Dividing by `p ≡ 3 (mod 4)` keeps `4 | k`.

The finite residue checks use kernel `decide` on small closed goals: the ZMod 2 table in `Quaternion.lean:110`,
the mod-4 table in `Parity.lean:64`, and `Atlas.lean:1088`.

## Audit of the contribution

* **Files.** Relative to origin/main the PR only adds files, all ten under `ZInQKernel/Contrib/OneProof/`:
  `JonesPall.lean`; `JonesPall/{Quaternion,Descent,Parity,Representation}.lean`; `JonesPall/{NOTICE.md,
  Mathlib.LICENSE}`; `LegendreThreeSquares/{Atlas.lean,LICENSE,NOTICE.md}`. The PR changes no existing (pinned)
  file. `JonesPall.lean` imports the defining module `ZInQKernel.Contrib.OneProof.TYZLemma29Mod2`, not
  `ZInQKernel.OneProof.Main`. The file is named `JonesPall.lean` rather than `<StatementName>.lean`
  (`JonesPallX2Y2Z16.lean`). This is cosmetic and harmless.
* **No build-time code.** The six `.lean` files contain no `#eval`, `run_cmd`, `initialize`, `syntax`,
  `notation`, `macro`, `elab`, `axiom`, `sorry`, `native_decide`, `implemented_by`, `extern` or `set_option`.
  `Atlas.lean` uses the module system (`module`, `public import`, `@[expose] public section`), which runs no code.
* **Shared provider.** `LegendreThreeSquares/{Atlas.lean,LICENSE,NOTICE.md}` have the same git blobs (b0355816,
  010649b7, 2960f767) as PR #36's head 47ca4df2 and as origin/wip/leaf-fold32b. The source is
  facebookresearch/atlas-lean at 8860f7b5, Apache-2.0 according to the NOTICE (the license itself was not
  re-read here). Merging PR #38 after PR #36 or leaf-fold32b therefore adds no conflicting content.
* **Composing with leaf-fold32b.** leaf-fold32b (not yet on main) already removes `hL3s` with PR #36's
  `legendreThreeSquares_proof`. It keeps the binder `hJP` with the same type, and its `TYZLemma29Mod2.lean` blob is
  identical. On that `Main` the fold is the same one-line substitution plus the import. **UNCHECKED** (no built
  tree of that branch on this host).

## Autofold spec and leaves

* `scratch/jp-compile/autofold.json`:
  `{"field": "hJP", "proof": "_root_.ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof"}` with import
  `ZInQKernel.Contrib.OneProof.JonesPall` and no leaves. `autofold.py --dry-run` rejects it with
  `not a field of the current bundles: ['hJP']`, as expected: autofold folds only bundle fields, and `hJP` is a
  `frozenTarget` argument. The fold is the manual edit in `FoldCheck.lean`.
* **New leaves: none.** The proof uses Mathlib and the in-tree port of a formal proof (atlas-lean's Legendre).
  Nothing is cited, so there are no printed-form ratings to give. For kinds.tsv, the row
  `frozenTarget hJP published ... LEAF LEAF` is removed with no replacement. The LEAF count drops by one (strict
  and strictest columns) and the GLUE counts are unchanged.

## Files

`scratch/jp-compile/`:

* `log.md`: the results log.
* `Discharges.lean` and `Discharges-output.txt`.
* `FoldCheck.lean` and `FoldCheck-output.txt`.
* `autofold.json` and `autofold-dryrun.txt`.
* `build-excerpt.txt`.
