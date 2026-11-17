# pic-dict (the three Pic-dictionary rows), status

**Main result.** `weilPairingMumford` and `phiAmpleIsogeny` are **each replaced by printed leaves plus Lean glue**.
Folding both gives −2 strict and −2 strictest GLUE on the lf31 rating (autofold dry-run `37/11 -> 44/9; strictest
37/11 -> 44/9`; on this base `40/8 -> 45/8; strictest 39/9 -> 45/8`, no `--allow-rise`; spec
`scratch/pic-dict/autofold-both.json`, dry-run module compiles).
- **7 leaves, shared by the two rows:** Mumford's displays over an algebraically closed field (`X : AbVar k`,
  `Pic⁰` = translation-invariant classes, `ē_n` by its formula): §6 Cor. 4, §6 App. 1, §8 (iv), §8 Thm 1,
  §20 (well defined, bilinear), §20 (nondegenerate), §23.
  - `phiAmpleIsogeny_final` uses two of them (§6 App. 1, §8 Thm 1). `weilPairingMumford_final` uses all seven.
  - Locators UNVERIFIED.
- **Proved in Lean** (`ZInQKernel/Contrib/OneProof/PicDictionary.lean`; builds; standard axioms; `#discharges`
  reports the fields):
  - **L5** (fppf sieves at `Spec K̄` are maximal);
  - base change to `A_K̄`;
  - the dictionary `B(K̄) ≅ Pic⁰(A_K̄)`, including "`K̄`-points of `Pic⁰` are translation-invariant" (vendored
    Kleiman 9.2.5 plus rigidity on `A × Pic⁰`);
  - **transport of Mumford's formula** (pseudofunctor coherence). This proves the Galois, adjoint and
    compatibility clauses;
  - `finiteOfFiniteKerPts`, ampleness under base change, `𝒪 = f_*𝒪` universally, products geometrically integral;
  - smooth ⇒ geometrically reduced.
  - Consumers unchanged.
- **`picZeroAbVar`:** reduced to four statements, with the open-subgroup glue proved (`picZeroAbVar_of_leaves`).
  - Three are printed: Kleiman 9.4.8, SGA 3 VI_A 2.4, Kleiman 9.5.4.
  - **`picZeroSmooth` (`Pic⁰_{A/K}` smooth) is pending reading**. Mumford §13 has it only over `K̄`.
  - Spec `autofold-all.json`: lf31 `37/11 -> 47/9`; it would be −3 once `picZeroSmooth` clears.
  - Smoothness of `B` is two theorem steps, nonsingular to smooth and descent (report §3).

**Remains.** Reading: a one-print source for `picZeroSmooth` (BLR 8.4 / Milne 1986 §10), and all locators.

Report: `docs/research/pic-dict.md`; log `scratch/pic-dict/log.md`.
