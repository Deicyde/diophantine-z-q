# scratch/pic-dict

Deliverable: `ZInQKernel/Contrib/OneProof/PicDictionary.lean` (report `docs/research/pic-dict.md`).

- `Verbatim.lean`: verbatim copies of the three rows, `rfl`-checked against `T09Pic` (compiles).
- `Discharges.lean` / `discharges.txt`: `#discharges` against the final module.
- `autofold-both.json` (recommended: folds `weilPairingMumford` and `phiAmpleIsogeny`), `autofold.json` (Weil only),
  `autofold-all.json` (all three rows); `FoldDryRunBoth.lean`, `FoldDryRun.lean`, `FoldDryRunAll.lean`: the dry-run
  modules (line 1 stripped), all compile.
- Development copies, each merged into the Contrib file and compiled there:
  - `Core.lean`: L5, the dictionary, the leaves at `A_K̄`, the first assemblies;
  - `Transport.lean`: coherence and the Galois transport;
  - `Finite.lean`, `Dual.lean`, `Compat.lean`, `AlgClosed.lean`, `TranslInv.lean`, `Ample.lean`, `PicZero.lean`,
    `GIProd.lean`, `PushU.lean`.

  They import `ZInQKernel.Contrib.OneProof.PicDictionary`, so against the final module they clash on names. They
  compiled at their merge.
- `log.md`: results log.
