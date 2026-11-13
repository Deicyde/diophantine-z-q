# leaf-adopt3 (fleet note)

**Result: `scratch/h-decomposition/Leaves.lean` has no `sorry`.** The top-level theorem is
`HSyn.sixContactMin_of_leaves (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces) :
ZInQ.SixContactMin`. Its hypotheses are exactly these three bundles, and it uses only the
standard axioms. So H follows from **58 literature leaves** (23 research-level, 35 textbook; 56
concrete, with R17 and R1(b) still `opaque`) and **10 named glue Props** (`GluePieces`), which
the project must still prove.

**What compiles** (VERIFIED, `lake env lean scratch/h-decomposition/Leaves.lean`, 2026-11-13
02:20): exit 0 in 452 s, 34 024 lines, 0 errors, no `sorry`, 175 `#print axioms` lines all
`[propext, Classical.choice, Quot.sound]`, 2 `opaque`, no `axiom`.

**What was folded in:**
- **g0-split's proof of G1-G17, G19.** R18, R22 now come from the bundle, through the glue piece
  `HeightCopiesAgree`.
- **Proved, and removed from the bundle:** T13, T19 (t-skolem-kw), T22 (t-different), T30 from
  T16(a) (t30-adelic).
- **Narrowed:** T17 (cyclic Kronecker–Weber), T18 (Chebotarev, existence form).
- **Made concrete:** T10 (t10-etale, Galois-equivariant).
- **New leaves:** T36-T40 (x1-belyi; they prove `X1ModelExists`, `BelyiX1`) and T41 (Néron models
  exist, h5-neron's N1).
- **Glue proved:** C9 (c9-rhof); `VSurjOfSurjective` (e1-sub); `SemisimpleBaseChange`
  (glue-ssbc); `HodgeLatticeTheorem` from two Props and `DimBaseChange` (hodge-lattice); H5's
  Néron identity (h5-neron; H5 stays a leaf); pi0-x6's reduction (R1's clause kept).
- **New proofs in this task:**
  - g0-split's piece `X1BelyiOnModel`, from `BelyiX1` by transport;
  - piece `HeightAdditivity`, from T41, H5 and h5-neron's `ProductModelHeight`, which replaces it
    as a piece.
- **Docstring repairs:** rv-leaves48 and factcheck-w34b (12, script-applied); h-decomposition.md
  updated (leaf table, counts, glue table with the pieces, WPs, remaining work).

**Diff check** (script `stmt_diff.py` against 883c4ddf): only `TextbookLeaves`,
`glueOutputs_of_leaves` and `sixContactMin_of_leaves` changed, and the T10 `opaque` was removed.
Every leaf `def` is unchanged. Bundle fields were only made concrete (T10), removed because proved
(5), narrowed to weaker forms (T17, T18) or added (T36-T41). Folded copies match their task files
(`fold_diff.py`), with four reported exceptions (references to identical originals, one dropped
`rfl`).

**What remains:**
- The ten glue pieces: `DimFinite`, `DimBaseChange`, `FibreSimple`, `ProductModelHeight`,
  `StableHeightBaseChange`, `ProductExists`, `ReverseIsogeny`, `ThetaPointOfFibre`,
  `ModularConstituent` (the bulk), `HeightCopiesAgree`.
- The placeholders R1(b) and R17.
- G1-adelic is not copied into `Leaves.lean`.
- The task's named rows C2/E1/WP3/WP5/WP13 are not among factcheck-w34b's items. I corrected
  them from their real sources (glue-ssbc, loc-fix).

Report: docs/research/leaf-adopt3.md. Log: scratch/leaf-adopt3/log.md.
