# gr-isogdeg: fleet summary

**Verdict.** The last step on Gaudron–Rémond's row is proved, so `gaudronRemondThm14An` is now a direct
instance of the print: **−1 GLUE**. With this, r3-residual's full −3 stands.

Two theorems compare, for an isogeny `φ : A → B` of abelian varieties, the geometric points of the kernel
with the degree of `φ` as a finite morphism. That degree is `finDeg φ`, Mathlib's `Scheme.Hom.finrank` of
`φ` at the generic point of `B`, which is `[K(A):K(B)]`.
- `isogDeg_le_finDeg`: `# ker φ(K̄) ≤ deg φ` over any field.
- `isogDeg_eq_finDeg`: `# ker φ(K̄) = deg φ` in characteristic 0.

**What compiles.** Everything below is VERIFIED, with the standard axioms only.
- **File.** `ZInQKernel/Contrib/OneProof/GaudronRemondIsogDeg.lean` (namespace `ZInQ.GRIsogDeg`, no
  `sorry`). It builds together with `Main` and `Discharges` (16049 jobs).
- **New leaf.** `GaudronRemondThm14AnDeg` is GR Thm 1.4 over r3-residual's `IsAnStableHeight`, with the
  printed degree `finDeg`. Rating: **printed form**. `gaudronRemondThm14AnDeg_iff_an` proves it equivalent to
  r3-residual's leaf, so it is provably never stronger.
- **`#discharges`.** `DISCHARGES [OpenResearchLeaves40.gaudronRemondThm14Printed] by
  ZInQ.GRIsogDeg.gaudronRemondThm14Printed_of_anDeg_final`, which still assumes only
  `[ZInQ.GRIsogDeg.GaudronRemondThm14AnDeg]`.
- **Autofold.** The spec is `scratch/gr-isogdeg/autofold.json`. The variant `autofold-after-r3.json` is for
  use if r3-residual is folded first.
  - The dry run gives `16/15 → 16/15`. It shows no change because `kinds.tsv` already rated the old row LEAF.
  - The generated module compiles, and `sixContactMin_of_open59` has the standard axioms.

**What remains.**
- Nothing on this row.
- Optional extras, not needed by the consumer: flatness of isogenies in Lean, and
  `finDeg = Module.finrank K(B) K(A)`.

Report: `docs/research/gr-isogdeg.md`; log: `scratch/gr-isogdeg/log.md`.
