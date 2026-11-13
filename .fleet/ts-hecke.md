# ts-hecke (2026-11-13): the five Hecke Props under CoverModelOfHecke

**Verdict.** All five Props (`HeckeIrreducible`, `HeckeNormalizationIrr`, `HeckeDegree`,
`HeckeBranch`, `HeckeNoVertRam`) are true. None was changed. Four are reduced in Lean, and
`HeckeDegree` is proved outright from an existing leaf.

**Results:**

- **`HeckeIrreducible`** was marked SPECULATIVE and is now settled by computation. Y₃ has exactly
  two geometric components (2 orbits of 𝒪^× on {±}×(𝒪/3𝒪)^×), and complex conjugation swaps
  them (`pi0_check.py`). In Lean it is reduced to the leaf R1conn (`Y3Connected`: Y₃ is
  connected over ℚ; Shimura/Deligne π₀ with reciprocity). The leaf is also necessary (converse
  proved).
- **`HeckeDegree`** is proved from the kernel's textbook leaf `TorsionStructure` (T5, Mumford §4)
  alone. A π-fibre has ≤ 4·81 = 324 classes, using aut-o-finite's 4 inner classes and the
  kernel's level torsor. `GenericFibreCount` (generic étaleness) is proved from Mathlib.
- **`HeckeNormalizationIrr`** is reduced to `CurveNormChart` (curve theory: finite map and
  normalization chart; no moduli, no Galois) plus T5. Two things are proved:
  - fibre transitivity under R1hecke, using 𝒪^× → (𝒪/3𝒪)^× onto (72 units, `decide`);
  - the Galois property (π-preserving automorphisms induce automorphisms of E/ℚ(X), then a count).
- **`HeckeBranch`** is reduced to two glue Props plus the leaves T5 and `R1R2fp`:
  - `CurveChartInf` (the chart at ∞);
  - `HeckeFibreSizes` (twist-fibre sizes 144/36/24/72, Baba–Granath §3.1).

  `RamOfFibreCount` (e·#fibre = degree for Galois extensions) is **proved** (`RamCount.lean`).
- **`HeckeNoVertRam`** stays open. The analysis is in report §6: two routes (Lemma NV, or good
  reduction), and an example showing that branch data alone cannot give it.

**What compiles.** `lake env lean scratch/ts-hecke/TSHecke.lean`: 0 errors. All 67
`#print axioms` lines are standard, with no sorryAx. The file contains prop-ts-glue's whole file
verbatim (`check_identical.py` ALL OK). The composite `TSHecke.propTSAll_of_tsHecke` replaces
prop-ts-glue's five Hecke Props by: Y3Connected, TorsionStructure, CurveGaloisChart,
CurveChartInf, HeckeFibreSizes, HeckeNoVertRam. The primed version takes CurveNormChart in place
of CurveGaloisChart. An independent read-only review found every new
Prop true.

**What remains.** Leaf R1conn (`Y3Connected`). Glue: `CurveNormChart`, `CurveChartInf`,
`HeckeFibreSizes`, `HeckeNoVertRam`. Report: docs/research/ts-hecke.md. Log: scratch/ts-hecke/log.md.
