# hecke-rest (2026-11-13): the four glue Props left by ts-hecke

**Result.** All four targets are true and none was changed. Three are now **theorems** and one
is reduced; everything compiles with standard axioms only.

- **`CurveNormChart`, `CurveChartInf`, and hence ts-hecke's `CurveGaloisChart`, are proved.**
  They use Mathlib only and have no leaf and no remaining glue (`HeckeRestCurve.curveNormChart`,
  `curveChartInf`, `HeckeRestAll.curveGaloisChart`). The proof runs through these steps:
  - the two charts of `π` are proper (valuative criterion);
  - they are locally quasi-finite, from the finite `ℚ̄`-fibres and Stacks 02UP;
  - so they are finite and affine (Mathlib's ZMT corollary);
  - smooth curves are normal (local rings at closed points are DVRs);
  - no closed point of a smooth curve is open, which gives dominance and irreducibility;
  - the chart at `∞` is built for the given `E` (function-field identification through the chart's
    image).
- **`HeckeFibreSizes`** is proved from `TorsionStructure` and three new **leaves**:
  - `QMAutCard`: `|Aut(A,ι)|` is 4, 6 or 2 by CM type (Shimura's classification);
  - `SerreRigidity3`: Serre's lemma;
  - `ALFixedPoints`: the fixed points of Atkin–Lehner involutions on `X₆` are CM points by `ℤ[i]`,
    `ℤ[ζ₃]`, `ℤ[√−6]`.

  The count `#fibre · s · a = 288` is compiled. The computation (`fibre_sizes.py`) gives sizes
  144/36/24/72.
- **`HeckeNoVertRam`** is reduced to `HeckeVertWitness` (one unramified vertical prime). Galois
  transitivity over `ℤ[X]` is compiled. Honest scope: the witness is equivalent to the target, and
  its content is good reduction of `Y₃` (Morita/Carayol) or Lemma NV.

**What compiles** (`lake env lean`, 0 errors):

- `scratch/hecke-rest/FibreSizes.lean`;
- `NoVert.lean`;
- `CurveChart.lean`;
- `HeckeRestAll.lean` (all of `TSHecke.lean` plus the new parts), with
  `coverModelOfHecke_of_heckeRest : Y3Connected → R1R2fp → TorsionStructure → QMAutCard →
  SerreRigidity3 → ALFixedPoints → HeckeVertWitness → CoverModelOfHecke` and
  `propTSAll_of_heckeRest`.

**What remains:**

- the leaves `QMAutCard`, `SerreRigidity3`, `ALFixedPoints`, plus ts-hecke's `Y3Connected`,
  `R1R2fp`, `TorsionStructure`;
- the glue `HeckeVertWitness`, which needs the good-reduction leaf.

**Review:**

- An independent model review confirmed Part 1 and Part 2, with one citation fix.
- A self-review found and fixed an empty-`Y` counterexample in two intermediate curve Props, both
  since proved.

Report: docs/research/hecke-rest.md.
