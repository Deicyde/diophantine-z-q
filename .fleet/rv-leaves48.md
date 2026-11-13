# rv-leaves48 (fleet summary)

**Verdict.** None of the 48 concrete leaves of `scratch/h-decomposition/Leaves.lean` (the 56
concrete fields of `ResearchLeaves` and `TextbookLeaves`, after leaf-adopt) is OVER-STRONG,
VACUOUS or MISSTATED; all are OK, each the published statement or a consequence over genuine
definitions. Residual risk sits outside the Lean text:
- primary sources unread (R20 Faltings Lemma 5, R6 at m = 3, R7-R9, Bost's display);
- the QM leaves need rv-qm-polar's Lemma P (unique principal polarization of the fixed type μ);
- H5 carries the definitional risk of `stableFaltingsHeight`. A defect would make H5 false
  (bundle unsatisfiable), never R19-R21 false.

Report: docs/research/rv-leaves48.md, with the per-leaf table, worst residual risk first.

**Findings, no leaf text changed.** Proposed text is in scratch/rv-leaves48/Repairs.md.
1. `X1ModelExists` is in neither bundle and is unproved, so r16 and t34 cannot be used by the
   glue yet. Add it as a leaf (Shimura's canonical model with a rational cusp) or prove MC4 + MC10.
2. "Not yet known non-vacuous" (bundle docstring 19181; h-decomposition.md) is the wrong
   description of R19-R21. The height is `⊤` or the true value, and only H5 can expose a defect.
3. Docstrings need fixing:
   - the QM premise without its Rosati type (19112);
   - T23 called "Exact";
   - t16b's normalization (and an error in rv-leaves-b about θ ↦ θ⁻¹);
   - T31's citation.
4. Glue note: two distinct `GaloisRep` structures (HSyn for r14/r15, PkgI4 for r13/PanFor).

**What compiles.** Leaves.lean compiles: EXIT 0, one `sorry` (`glueOutputs_of_leaves`). It first
needs `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.Compiler.Precision.HeightConstant`.
scratch/rv-leaves48/Probes.lean (copy plus probes) compiles with EXIT 0, standard axioms. It proves:
- height `= ⊤` iff no metrized model;
- the `⊤` case trivializes R21 and empties R19/R20;
- H5 forces a metrized model;
- the zero form is not an eigenform;
- the bundle field types;
- μ² = −6;
- the bundles plus `X1ModelExists` give `ModCurveLeaves`.

**What remains.** Positive non-vacuity witnesses for scheme-level hypotheses (QM surfaces,
metrized models, models of X₁(N)) cannot be built in Lean today. The unread locators stay
UNVERIFIED.
