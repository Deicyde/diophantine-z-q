**leaf-fold (2026-11-13): the closed leaves folded in; the open bundles.** (VERIFIED: `lake env
lean scratch/h-decomposition/Leaves.lean`, see `docs/research/leaf-fold.md`.)
- **The file now imports the closed proofs.** Since the kernel port `ZInQKernel/HDecomp/` declares
  the file's names at the root, the whole file is wrapped in `namespace HDec` (every name below is
  `HDec.…`, e.g. `HDec.HSyn.sixContactMin_of_open`); it imports seven `ZInQKernel/Contrib/` modules
  and `ZInQKernel.HDecomp.Textbook.BrauerNesbitt`.
- **New top-level theorem** `HSyn.sixContactMin_of_open (r : OpenResearchLeaves)
  (t : OpenTextbookLeaves) (gp : GluePieces) : ZInQ.SixContactMin`, standard axioms only. Its
  hypotheses are exactly the open leaves and the ten glue pieces.
- **Proved textbook leaves, no longer hypotheses** (each a theorem of the file, from a closed proof):
  T2 (t-brauer-purity, proof copied in), T15 (t1415-tc), T16(a) (lkw), T17 (kw-new), T18
  (cheb-bridge), T20 and T21 in global form (diff-bridge), T25 (t25-newform), T31 (t31-unram); with
  T13, T19, T22, T30 (proved earlier) and T12, T32 (glue). T14(a′), T14(b′) are reduced to
  t1415-tc's `KummerIndexBound` but stay leaves. Each Contrib Prop is checked against the bundle's
  field: definitionally (the `exact` conversion) and syntactically (`#hdec_same`, which compares
  the definitions and everything they mention up to the prefix `HDec.`; results in
  `docs/research/leaf-fold.md`).
- **Statement repairs.** R10 is now `PkgI4.DeRhamComparisonHT` (with g9-derham's multiplicity-0
  clause), R14 is g0-mod-galois's `R14Det` (with the determinant); g10-odd's concrete G10
  (`G0Galois.G10GlueConcrete`, `ConjTwistNontrivial`) is recorded (it is part of the glue piece
  `modularConstituent`, not a hypothesis of G0).
- Counts: **open: 23 research-level leaves** (all; 21 concrete, R1(b) and R17 placeholders) and
  **27 textbook leaves** (of 35; T16 counted open for its part (b)), **50 in all**; **proved: 8
  textbook leaves** (T2, T15, T17, T18, T20, T21, T25, T31) and T16(a). Bundles: 26 + 26 fields.
