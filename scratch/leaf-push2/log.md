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
- 19:45 Added R22 section: `cptObj`, `CPts` (complex points of an `AbVar` at `σ`, Mathlib group
  structure), `cEvalAt`, `cDom`, `IsUniformization` (def-faltings' AN3 predicate for `AbVar`),
  `IsSiegel` (𝔥₂), `IsPeriodMatrix` (∃ ℂ-linear T, T(Λ) = Ωℤ² + ℤ²: encodes every principal
  polarization + symplectic basis, no polarization object), `Char2`, `thetaConst` (θ[a;b](0,Ω) as a
  `tsum`), `absLogHeight`, `pazukiC2` (copied), **`R22_Pazuki`** (upper-bound consequence, sup-norm
  height of any algebraic representative of the theta-null point), `R22_plus3`, `isSiegel_I`.
- R3 section: 𝒪, `QMStr` (copied from leaf-qm-fp), IC2..IC10, `IsGenus2`, `OnQMLocus` (copied from
  hdec-elementary), Igusa `IgJ2..IgJ10` (new), `LinYangTuple` (literal Lin–Yang J-tuple, weights
  1,2,3,5), **`linYangTuple_onQMLocus`** (proved: Lin–Yang's J-tuple with scaling c² is exactly
  hdec-elementary's Igusa–Clebsch `OnQMLocus`, so the convention of the two is consistent; VERIFIED
  by compilation), `onQMLocus_of_linYangTuple`, `linYang_j_eq` (j = 3779136 I₁₀²/I₄⁵ from the
  tuple), `sextic`, `HasSexticModel`, **`R03_LinYang`** (over ℂ: QM surface ≅ Jac(C), C on the
  family at j ≠ 0, or ≅ E₁ × E₂), `R03_LinYang_algClosed` (glue target, Lefschetz), `R03_of_algClosed`.
- T section: `UniformizationExists` (AN3 for AbVar), `T11a_RiemannEnd`, `T11b_Rigidity`,
  `IsComplexConj`, `T12_ComplexConjEigen` (form used at G10; glue target), `exists_isComplexConj`
  (proved), `T10_groupIso` (over Mathlib's pro-étale `Scheme.EllAdicCohomology`).
- FINDING (VERIFIED, read in .lake/packages/mathlib/Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean):
  Mathlib v4.35 defines ℓ-adic cohomology `Scheme.EllAdicCohomology X ℓ n` (pro-étale, Bhatt–Scholze
  Def. 6.8.1) as an `AddCommGroup` only: no ℤ_ℓ-module structure, no pullback maps, so no Galois
  action. prereq-survey.md ("ℓ-adic étale cohomology: missing") is out of date on this point.
- 19:48 Compile: `lake env lean scratch/leaf-push2/LeafPush2.lean`: exit 0, no errors, no warnings;
  every `#print axioms` = [propext, Classical.choice, Quot.sound]. VERIFIED. (Fixes on the way:
  `ι` is a reserved token under the opens of Part I, renamed `emb`; `IsComplexConj` takes the
  `AlgEquiv` type, not `Field.absoluteGaloisGroup ℚ`.)
