# eps-splitting: fleet summary

**Result.** Proved in Lean (no `sorry`, standard axioms): for a negative fundamental discriminant `D`, a quadratic
field `K` with `δ² = D`, and every prime `p`, the Kronecker symbol `ε_D(p)` (hgz-steps' `HGZSteps.epsD`) is `1`, `−1`
or `0` according as `p` splits, is inert or ramifies in `K`.
- Theorem: `ZInQ.EpsSplit.splitType_epsD`.
- The three predicates are defined through prime ideals of `𝓞 K`: `primesOver`, `IsPrime`, `ramificationIdx`.
- The proof shows `𝓞_K = ℤ[(D+√D)/2]` and then uses Mathlib's Kummer–Dedekind theorem
  (`primesOverSpanEquivMonicFactorsMod`).
- Corollary `quadChar_eq_epsD`: the quadratic character of `K` equals `ε_D`.

**Use.** The new leaf `ZInQ.GZSplit.GrossZagierCurveCdSplit` is hgz-steps' `GZSch.GrossZagierCurveCd` with two
changes, both as in Gross–Zagier:
- the Heegner hypothesis reads "every `p ∣ N` splits in `K`";
- the twist is by the quadratic character of `K`.

The two leaves are proved equivalent in Lean. `grossZagierAlgOptCd_of_split` discharges the binder `hGZ`. The
reviewer's possible step on `ε_D` is gone. The leaf is rated LEAF, printed form (direct instance); its count is
unchanged relative to hgz-steps.

**What compiles.**
- New files: `ZInQKernel/Contrib/OneProof/GrossZagierSplit.lean` and `GrossZagierSplit/QuadSplit.lean`.
- `lake build +Main +Discharges +GrossZagierSplit`: 14,283 jobs, no errors.
- `#discharges`: `DISCHARGES [hGZ] by ZInQ.GZSplit.grossZagierAlgOptCd_of_split`, still assuming
  `[GZSplit.GrossZagierCurveCdSplit]`, with standard axioms.
- FoldCheck (`frozenTarget` with `hGZ` retyped): standard axioms.

**What remains.**
- The manual fold: `hGZ` is a binder, so follow `scratch/eps-splitting/fold-spec.md`. `autofold.json`,
  `kinds-row.tsv` and `locators-row.md` are ready.
- The GZ page locators are still UNVERIFIED: there is no copy on this host.

Report: `docs/research/eps-splitting.md`; log: `scratch/eps-splitting/log.md`.
