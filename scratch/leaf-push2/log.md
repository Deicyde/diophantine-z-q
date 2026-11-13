# leaf-push2 results log

Compile command: `lake env lean scratch/leaf-push2/LeafPush2.lean` (one Lean process at a time).

## 2026-11-12

- 19:36 `LeafPush2.lean` Part I: def-faltings §§1-18 + H5 section copied (namespace
  `ZInQ.LeafPush2`), local `AbVar` replaced by the kernel's `PkgI3.AbVar` (identical fields;
  `PkgI3.AbVar.baseChange`, `.dim` identical). Part II: `IsCurve`, `IsJacobian`, `JacobianExists`,
  `IsBelyiFunction` copied from leaf-modcurves; new `ffStructMap`, `ffAlgebra` (K → K(X)).
  Part III: `R18_Javanpeykar` (EReal upper bound on `stableFaltingsHeight J`, J Jacobian of a curve
  over a number field, g = dim J ≥ 1, Belyi function t, d = [K(X):K(t)] > 0), `R18_real`,
  `javanpeykarBound_pos`, `javanpeykarBound_mono` (proved). COMPILES (exit 0, 2 min 14 s; one
  linter warning on ffAlgebra, fixed by `@[instance_reducible]`). VERIFIED.
