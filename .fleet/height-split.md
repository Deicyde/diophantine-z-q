# height-split (2026-11-14)

**Result.** All six assigned rows are Lean theorems from published-form leaves plus named glue:
H-14 (R18), H-16 (R20), H-17 (R21), H-18 (R22), H-19 (`StableHeightFinite`) and H-3 (`R5fpCount`).
H-15 (R19) is done as a bonus. No `sorry`; all axioms are standard.
- **Main file:** `scratch/height-split/HeightSplit.lean`. It imports the kernel rows and does not
  restate them.
- **H-3:** `scratch/height-split/R5Count.lean`.
- **Report:** `docs/research/height-split.md`, which has the table, the H-17/H-18 differences from
  the prints, and the glue list.

**Key step.** The file defines semistable reduction and Faltings' published stable height
(`IsStableFaltingsHeight`: the height of a Néron model over a field of semistable reduction). It then
proves `IsStableFaltingsHeight A x ↔ stableFaltingsHeight A = x` from three inputs:
- the kernel leaf N1;
- two SGA 7 IX leaves, SS1 (semistable reduction theorem) and SS2 (base change of `𝒩⁰`);
- the kernel's proved H4a, H4b, M6 and `NeronModelMinimal`.

The kernel leaf N2 follows as a corollary.

**Leaves only** (`heightRows_leavesOnly`):
- R22 (`r22_of_upper`), from the upper half of Pazuki's Cor. 1.3(2) with the ℓ² theta height;
- R20 (`r20_of_leaves'`), from Lemma 5 for base changes and SS3;
- R19.

**Glue still open:**
- **R21 and the `≠ ⊥` half of H-19:** the kernel's `AnalyticUniformizationUnique`.
  `MetrizedDimUnique` is **proved** by a 2-torsion count.
- **R18 and the `≠ ⊤` half of H-19:** `NeronMetrizable`, reduced to the kernel's
  `AnalyticUniformizationExists`, `UniformizationDim` and `MetrizationOfUniformization`.
  `UniformizationDim` is false without lattice hypotheses, so it was stated with them.
- **R5fpCount:** `QMPairEmbeddingCorrespondence` (Shimura uniformization, an `Equiv`), together with
  the leaf `EichlerOptimalEmbeddingCount` (count modulo `𝒪^×`).

`heightRows_of` bundles all six height rows.

**Verdicts.**
- No row is false. H-17 and H-14 contain finiteness clauses about the project's definition (`≠ ⊥`,
  `≠ ⊤`); these are isolated as the H-19 glue.
- H-18 is weaker than the printed corollary in four ways. The risk: if Pazuki's coordinates are
  second-order thetas, the row overstates the print by about `log 4`. A corrected row is in report §8.
- The new definitions are satisfiable: they hold at the zero abelian variety (§I, compiled).

**Remains.** Locators UNVERIFIED: SGA 7 IX 3.3/3.6, Bost's display, Lemma 5 (operative source
Raynaud VII 2.1.3), Eichler/Vignéras numbering, Pazuki Def. 2.6. The four glue Props above are deep
(complex analysis, Shimura theory) and are not attempted.
