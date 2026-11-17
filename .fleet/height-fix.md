# height-fix (fleet note)

**Result.** Review items (1) and (2) are closed in Lean. Item (3) is closed in the direction the print needs, and
one new glue Prop remains for the other direction. The fold is −1 GLUE against the re-rated base (target was −2).
Everything is VERIFIED: compiled, standard axioms, `#discharges` shows both fields discharged.

The new file `ZInQKernel/Contrib/OneProof/PrintedStableHeight.lean` (49 KB, namespace `ZInQ.HeightFix`) imports
height-dict's `HeightDictionary` and dict-models' `RaynaudSemistableOr`.

- **(1) Soundness.** The new metric `IsPrintedMetricSq` requires that the measure `(i/2)^g η∧η̄` exists and that
  every such measure has mass `r`.
  - Existence is proved for every group model, every τ and every η ≠ 0 (`existsUnique_isPrintedMetricSq`, from
    T35).
  - `isPrintedStableHeight_iff` no longer takes `NeronMetrizable`; it is proved inside from T35.
- **(2) R3 is now a definition plus lemmas.** `IsFormMeasure` means a finite measure with density `|τ l|²`
  at every point, in algebraic coordinates translated to that point. Invariance is not assumed. Proved:
  - uniqueness of measures with given local densities (`eq_of_density`), which gives invariance;
  - charts (`exists_chart`, inverse function theorem) and holomorphic coordinates (`chartAt_comp_hasStrictFDerivAt`);
  - Haar identification with `|c_τ η|² covol(Λ)` (`isPrintedMetricSq_iff`).
- **(3) Semistability.** `IsSemistableRes` is SGA 7 IX 2.2/3.2 over `k(𝔭)` (dict-models' general-torus form).
  - The ascent `k(𝔭) ⇒ k̄` is proved (04KV). It gives printed ⇒ kernel.
  - The fields need kernel ⇒ printed, i.e. the descent `k̄ ⇒ k(𝔭)`, which is left as glue
    `SemiAbelianDescendsPerfect` (Chevalley over perfect fields). It may become a leaf if SGA 7 IX prints the
    criterion "semi-abelian iff over k̄" (needs a reading).
- **Leaves.** `BostLowerBoundPrinted` and `GaudronRemondThm14Printed` are both printed form: the old rows,
  verbatim, over the printed height. The new glue row is `semiAbelianDescendsPerfect`.
- **Optional.** Javanpeykar and Pazuki rows over the new height are also discharged.

**Checks.**

- `scratch/height-fix/discharges.txt` holds the `#discharges` output.
- `scratch/height-fix/autofold.json` is the spec. Its dry run needs `--allow-rise` on this base (34/11 → 34/12,
  because both rows are still LEAF here). It is 32/13 → 34/12 on the re-rated base. `FoldDryRun.lean` compiles.
- Fold order: dict-models first. This spec replaces height-dict's specs; height-dict's own
  `IsPrintedStableHeight` keeps the defect.

**Remains.**

- Prove `SemiAbelianDescendsPerfect`, or read SGA 7 IX §2.
- Statement checks of the two leaves.
- The locators.md rows (proposed in the report, §5).

Report: `docs/research/height-fix.md`.
