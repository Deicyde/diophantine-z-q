# metrization results log

Start 2026-11-13 04:08 PST. Base 2dd83306 (wip/integrate-w36b). Targets (verbatim from
scratch/g0-heightadd/part_heightadd.lean, part_prod.lean): `ZInQ.G0HeightAdd.MetrizationDimUnique`,
`MetrizationExists`, `ProductMetrizationGeo`.

## Run 1: ExtLine.lean (Mathlib only) — COMPILED 04:15 (3 min 10 s wall, load 28; 0 errors)
- `ZInQ.Metrization.eq_of_finrank_one`: for `R` comm ring, `F` a field, flat `R`-algebra, any
  `R`-module `C`, `0 < g`, `0 < g'`, `finrank F (F ⊗_R ⋀^g C) = 1`, `finrank F (F ⊗_R ⋀^{g'} C) = 1`
  ⇒ `g = g'`. Axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
  Proof: for `g < g + n`, pick `v` with `1 ⊗ ιMulti v ≠ 0` in `F ⊗ ⋀^{g+n}`, split `v = append a b`,
  swap one entry between `a` and `b`; right multiplication by `ιMulti b`, `ιMulti b'` separates
  `1 ⊗ ιMulti a` and `1 ⊗ ιMulti a'`, contradicting `finrank = 1` (flatness keeps
  `1 ⊗ ιMulti v ≠ 0` in `F ⊗ ⋀C`).

## Run 2: Metrization.lean (build.sh: Base.lean + ExtLine + part_dim) — FAILED (dot-notation
  on `ZInQ.Metrization.MetrizedModel.*` names; renamed to `metrized_*`).

## Run 3: Metrization.lean = Base.lean + ExtLine body + part_dim + part_g0dim + part_exists —
COMPILED 04:23 (41 s; 0 errors). `Base.lean` is byte-identical to scratch/g0-heightadd/HeightAdd.lean
(`cmp`), so the three target Props are the verbatim originals. VERIFIED.
- `ZInQ.Metrization.metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique` — PROVED, no
  hypotheses. Axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
  (g, g' ≥ 1: `eq_of_finrank_one` on `hodgeSpace = L ⊗_{𝓞_L} ⋀^g cotangent`, `L` flat over `𝓞_L`
  by `IsLocalization.flat`; g = 0 < g': `Φ : ℂ⁰ → 𝒢(ℂ)_τ` onto makes the points subsingleton,
  while a discrete kernel in `ℂ^{g'}` (ℝ connected) gives `Φ z ≠ 1`.)
- `part_g0dim.lean` = scratch/g0-dim/part_dim.lean l. 1-208 verbatim (namespace `G0Dim`) + `end`.
- `abVar_dim_finite` (def-faltings' `AbVar` has `dim ∈ ℕ`): PROVED from `G0Dim.dim_finite`. VERIFIED.
- new Props: `AnalyticUniformizationOfDim` (leaf: uniformization theorem at g = dim A),
  `JacDetDescends` (glue), `JacDetNondegenerate` (glue).
- `analyticUniformizationExists_of : AnalyticUniformizationOfDim → AnalyticUniformizationExists`,
  `exists_metrization_of_dim`, `metrizationExists_of : HodgeLatticeTheorem →
  AnalyticUniformizationOfDim → JacDetDescends → JacDetNondegenerate → MetrizationExists`,
  `metrized_dim_eq` (every metrization has g = dim A, same hypotheses): all compiled,
  axioms [propext, Classical.choice, Quot.sound]. VERIFIED.
