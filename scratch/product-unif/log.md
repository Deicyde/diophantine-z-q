# product-unif results log

## Run 1 (2026-11-13, from 05:51 PST)

- `lake build ZInQKernel.HDecomp.Faltings.Height`: success, 9051 jobs (VERIFIED).
- `Analysis.lean` (Mathlib only): `rcore`, `ccore`, `exists_isolated`, `exists_countable_add`,
  `rcore_sup_eq_top` (closed subgroups with `H₁ + H₂ = E` have `rcore H₁ ⊔ rcore H₂ = ⊤`; via
  `Measure.addHaar_submodule`), `isClosed_of_local` (subgroup cut out near 0 by functions continuous
  there is closed), `rcore_le_ccore` (identity theorem: real core of a subgroup cut out near 0 by
  holomorphic functions is complex), `eq_zero_of_mem_rcore_discrete`. Compile: 3 iterations
  (squeeze `simpa`, `TopologicalSpace.separableSpace_iff_countable`, `Function.comp_def`); final
  0 errors, 4/4 `#print axioms` standard (VERIFIED).
