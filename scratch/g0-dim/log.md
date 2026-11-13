# g0-dim results log

Base: wip/g0-dim at 883c4ddf, merged origin/wip/g0-split (c20fa62b) for `scratch/g0-split/`.

## Statements (copied verbatim from `scratch/g0-split/part_split.lean`)

- `HSyn.G0Split.DimFinite := ∀ (K : Type) [Field K] (A : PkgI3.AbVar K), ∃ n : ℕ, A.dim = (n : WithBot ℕ∞)`
- `HSyn.G0Split.DimBaseChange := ∀ (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : ZInQ.DefFaltings.AbVar K), (A.baseChange L).dim = A.dim`

## Compile outcomes (VERIFIED)

- run1 (`Alg.lean`, algebra part alone): 1 error (`RingHom.Finite.id` vs `(AlgHom.id K L).Finite`; fixed with `by exact`).
- run2 (`Top.lean`): 1 error (`spec_dim` needed explicit ring argument).
- run3-run5 (`Dim.lean`, merged): `pullback` needed a `: Scheme` ascription inside `topologicalKrullDim`;
  `LocallyOfFiniteType (𝒰.f i ≫ h)` not found by instance search across the `let 𝒰` (passed explicitly
  with `@`); `ENat` top case.
- run6: `lake env lean scratch/g0-dim/Dim.lean`: 0 errors, 0 sorry. `#print axioms`:
  `HSyn.G0Split.dimBaseChange`, `HSyn.G0Split.dimFinite`: `[propext, Classical.choice, Quot.sound]`.

- run7 (`Dim.lean` with the copied `PkgI3.AbVar.baseChange` and `G0Dim.pkgI3_dim_baseChange`): 0 errors;
  all three `[propext, Classical.choice, Quot.sound]`.
- Integration run1 (`SplitDim.lean` = `Split.lean` + `part_dim.lean`, via `build.sh`): 1 error, `η[..]`
  notation needs `open MonObj` (added).
- Integration run2: 0 errors, no `declaration uses sorry`, 2m38s. `#print axioms`, all
  `[propext, Classical.choice, Quot.sound]`: the seven of `Split.lean` plus `HSyn.G0Split.dimBaseChange`,
  `HSyn.G0Split.dimFinite`, `HSyn.glueOutputs_of_leaves_dim` (8 glue hypotheses), `G0Dim.pkgI3_dim_baseChange`.
  `SplitDim.lean` is generated (gitignored); rerun `scratch/g0-dim/build.sh` to recreate.

## Proved (VERIFIED, compiled in `Dim.lean`, Mathlib only)

| Lean name | statement |
|---|---|
| `G0Dim.ringKrullDim_eq_of_isIntegral_of_injective` | `A → B` integral, injective ⇒ `dim B = dim A` |
| `G0Dim.ringKrullDim_mvPolynomial_field` | `dim k[X_1..X_s] = s` |
| `G0Dim.ringKrullDim_tensor_field` | `R` f.t. over field `K`, `L/K` field ⇒ `dim (R ⊗_K L) = dim R` (Stacks 00P4 affine) |
| `G0Dim.ringKrullDim_le_of_finiteType` | `R` f.t. over a field ⇒ `dim R ≤ n` for some `n : ℕ` |
| `G0Dim.topologicalKrullDim_eq_iSup_of_openEmbedding` | dim of a space = sup over a cover by open embeddings |
| `G0Dim.dim_baseChange` | `X → Spec K` locally of finite type ⇒ `dim (X ×_K L) = dim X` |
| `G0Dim.dim_finite` | `X → Spec K` loc. finite type, quasi-compact, `X` nonempty ⇒ `dim X ∈ ℕ` |
| `HSyn.G0Split.dimBaseChange : DimBaseChange` | piece 2 |
| `HSyn.G0Split.dimFinite : DimFinite` | piece 1 |
| `G0Dim.pkgI3_dim_baseChange` | `dim (A_L) = dim A` for `PkgI3.AbVar.baseChange` |
| `HSyn.glueOutputs_of_leaves_dim` (in `part_dim.lean` only) | g0-split's main theorem without `hDimF`, `hDim` |
