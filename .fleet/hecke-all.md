# hecke-all (fleet summary)

**Result.** `ZInQ.Literature.HeckeContinuation` (an entire continuation of Mathlib's `L(C_d, s)`
for every `d ≠ 0`) is proved in Lean from Gauss's point count:
`ZInQ.Contrib.heckeContinuation_of_gaussPointCount : HeckeAll.GaussPointCount → Literature.HeckeContinuation`.
Also `ZInQ.Contrib.heckeContinuation_functionalEquation5_of_gaussPointCount`, which gives
`HeckeContinuation ∧ FunctionalEquation5`. Both are VERIFIED: `lake build` succeeds, there is no
`sorry`, and the axioms are `propext, Classical.choice, Quot.sound`. `GaussPointCount` is
bp-hecke-fe's statement, copied verbatim.

**What compiles** (`ZInQKernel/Contrib/HeckeAll/`):
- `LocalCd.lean`: Mathlib's `L(C_d, s)` for every squarefree `d`, odd or even (`LSeries_cd_eq'`).
  The new step is the minimality of `y² = x³ − (2e)²x` at 2, proved from `c₄`: over ℤ₂,
  `v₂(c₄) ∉ {1, 2, 3}`, while `v₂(c₄(C_{2e})) = 6` (`isMinimal_cdLocal_two`).
- `Iso.lean`: Mathlib's local polynomials do not change under a change of variables when `j` is
  integral (`localPolynomial_smul`). Hence `L(C_{m²d}, s) = L(C_d, s)` (`LSeries_cd_sq_mul`).
- `Continuation.lean`: `cdCoeff d n = J(d|n)·cdCoeff 1 n` (quadratic twist, every residue of `d`
  mod 8), the character `twChar d` on `(ℤ/4d)²`, `isLContinuation_of_squarefree`, and the final
  theorems.
- `HeckeFE.lean`: a verbatim copy of `scratch/bp-hecke-fe/HeckeFE.lean`, with the namespace renamed.

**Checks.** PARI (`scratch/hecke-all/twist_check.py`, 26 values of `d`, `n ≤ 300`): the twist
identity holds and no prime has multiplicative reduction, with 0 failures. A `GaussPointCount`
stated over another verbatim copy of the definitions is accepted by the theorem
(`scratch/hecke-all/ComposeTest.lean` compiles), so the gauss-proof task's result composes
directly.

**What remains.** `GaussPointCount` itself, which the gauss-proof task is proving. On integration:
add the one-line provider `ZInQ.Contrib.heckeContinuation := heckeContinuation_of_gaussPointCount
<gauss-proof>`, and keep a single shared copy of `HeckeFE.lean` (gauss-proof made a second copy).
Report: `docs/research/hecke-all.md`. Log: `scratch/hecke-all/log.md`.
