# rv-gluepieces2 (fleet summary)

**Verdict:** this was an adversarial review of the 27 fields of `GluePieces2`
(scratch/g0-assemble/G0Assemble.lean). No field is refuted. 21 are TRUE. 6 are UNSURE as stated:
4 `fibreComTrivial`, 10 `fibreQMPeriod`, 12 `fibreCoverExists`, 13 `kernelFieldExists`,
27 `modelG3G6` (its G6 half) and 28 `linkedTateData`. Report: docs/research/rv-gluepieces2.md.

**The cause:** G0Assemble.lean was generated from a copy of `Leaves.lean` taken before pin-apply.
Its `R1fpProps` still has 4 clauses, so rv-g0pieces' relabeling defect is live. Each of the six
fields quantifies over all triples `(Y, Φ, π)`, so as stated it is equivalent to an open arithmetic
statement.
- g0-assemble flagged fields 4, 10, 13 and 27 as QM-PIN.
- Fields 12 and 28 are in the same class. That is a new finding.

**Compiles (Lean 4.35 / Mathlib v4.35; 0 errors, no `sorry`, only standard axioms):**
- **Repair:** g0-assemble's parts compile over the post-pin-apply `Leaves.lean` olean, including
  `gluePieces_of_gluePieces2` and `sixContactMin_of_leaves2`. Only two demonstration lemmas needed
  an extra hypothesis.
- **Pin transfer (c9):** given pin-apply's `MobiusGlue`, each of the six fields follows from its
  statement for one triple.
- **Proved on G0Assemble's own constants:**
  - fields 3, 6, 14, 24, 25 and 26;
  - field 15 `BurnsideAbsIrred`, which was claimed as a leaf. It is new here (Schur plus Jacobson
    density over the algebraic closure, then a dimension count), so the leaf count drops by one;
  - field 22, from the bundle leaf `t17`.
- **Reductions re-elaborated on G0Assemble's constants:** fields 7, 8, 9, 12, 17, 19 and 20, plus
  18 reduced to `ConjTwistNontrivial`. This settles the transfer caveats: height-bc's proof works
  over the `DefFaltings.AbVar` copy, and g9-derham's works without its restated layers.
- **`HSyn.GluePieces3`** (15 fields) gives `sixContactMin_of_leaves3 r t gp : ZInQ.SixContactMin`
  (`scratch/rv-gluepieces2/final/c12_bundle.lean`).

**Remaining:**
- `G9Glue` needs `R10Weights` (Tate–Sen) and `AbVarBaseChange`, which are not among its
  hypotheses.
- `G10Glue` needs Artin comparison, which needs T35, T5 and T26; those are not passed to it.
- Fields 5 and 7 need the uniformization theorem, which is a leaf.
- Field 11 `thetaRatiosAlgebraic` and field 23 `carayolR17` are composites of published results.
  They need human audit as leaves.
- `MobiusGlue` is unproved here. Field 28 is TRUE only by a model argument (SPECULATIVE, report §4).
- Fields 1, 2, 5, 11, 16 and 23 got no Lean check.
- Recommended next step: regenerate G0Assemble over the pinned `Leaves.lean`, using
  `scratch/rv-gluepieces2/parts/` and `GluePieces3`.
