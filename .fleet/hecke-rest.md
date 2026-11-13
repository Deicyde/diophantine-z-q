# hecke-rest (2026-11-13): the four glue Props left by ts-hecke

**Result.** All four targets (`CurveNormChart`/`CurveGaloisChart`, `CurveChartInf`,
`HeckeFibreSizes`, `HeckeNoVertRam`) are true and none was changed. All four are reduced in Lean
with standard axioms; `HeckeFibreSizes` is **proved** from three new leaves.

- **`HeckeFibreSizes`** ⇐ `TorsionStructure` + leaves `QMAutCard` (|Aut(A,ι)| = 4/6/2 by CM
  type, Shimura), `SerreRigidity3` (Serre's lemma), `ALFixedPoints` (Atkin–Lehner fixed points
  on X₆). The count #fibre · s · a = 288 (72 level structures, Serre-free action) is compiled.
  Computation (`fibre_sizes.py`): sizes 144/36/24/72.
- **`CurveNormChart`** ⇐ `ChartProper` + `ChartQuasiFinite` + `ChartDominant` (curve glue);
  normality of smooth curves (`ChartNormal`, `ChartNormalD`) is now **proved**; finiteness from
  Mathlib's ZMT corollary.
- **`CurveChartInf`** ⇐ the same three + `InfFnField` (function field seen from ∞).
- **`HeckeNoVertRam`** ⇐ `HeckeVertWitness` (one unramified vertical prime; Galois
  transitivity over ℤ[X] compiled). Honest scope: the witness form is equivalent to the target;
  its content is good reduction of Y₃ (Morita) or Lemma NV.

**Compiles** (`lake env lean`, 0 errors): `scratch/hecke-rest/FibreSizes.lean`, `NoVert.lean`,
`CurveChart.lean`, and the integrated `HeckeRestAll.lean` (all of TSHecke.lean + new parts) with
`HeckeRestAll.coverModelOfHecke_of_heckeRest` and `propTSAll_of_heckeRest`.

**Remains:** leaves `QMAutCard`, `SerreRigidity3`, `ALFixedPoints` (plus ts-hecke's
`Y3Connected`, `R1R2fp`, `TorsionStructure`); glue `ChartProper`, `ChartQuasiFinite`,
`ChartDominant`, `InfFnField`, `HeckeVertWitness`. Review: an independent model review confirmed
Parts 1-2 (one citation fix); a self-review found and fixed an empty-`Y` counterexample in two
intermediate curve Props. Report: docs/research/hecke-rest.md.
