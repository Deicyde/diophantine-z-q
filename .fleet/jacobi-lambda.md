# jacobi-lambda (2026-11-15)

**Verdict: done.** gz-weil's printed leaf `ZInQ.GZWeil.JacobiLambdaDeriv` (Jacobi: `dλ/dt = πi λ θ₄⁴`,
`λ = θ₂⁴/θ₃⁴`, over Mathlib's `jacobiTheta₂`) is now the theorem `ZInQ.GZWeil.jacobiLambdaDeriv`
(standard axioms; no new leaves) in `ZInQKernel/Contrib/OneProof/GrossZagierHeegner/JacobiLambdaDeriv.lean`
(681 lines, imports `WeilTheta`).

Proof (elementary, Mathlib + one gz-theta bound): duplication formula for `jacobiTheta₂` by reindexing the double
series → Landen's identities and Jacobi's quartic `θ₃⁴ = θ₂⁴ + θ₄⁴` → nonvanishing of `θ₂, θ₃, θ₄` on ℍ →
the recursion `F(τ) = (θ₄²/θ₃²)(τ) F(2τ)` for `F = h'/h − (πi/4)θ₄⁴`, `h = θ₂/θ₃` → `F = O(e^{−π Im σ})` by
Cauchy estimates → `F = 0` by halving the constant along `σ ↦ 2σ`.

As a result, these are unconditional theorems: `X0.EtaModelDifferential`, `ModularParamC1` and gz-hl3's
`ShimuraCMParamCd` (the modular parametrization of every `C_d`). gz-weil's `C_d` split of `hL3` goes from 5 leaves
to 4 (`WeierstrassUniformization`, `HeegnerPointRationalCd` (composite), `GrossZagierFormulaCd`,
`GrossConjugationCd`); `scratch/jacobi-lambda/MainEdit.lean` proves `FrozenTarget` with them (standard axioms).

**What compiles (VERIFIED):** the contributor file (`lake build`, 11342 jobs, no warnings); `Check.lean` (verbatim
copy ↔ gz-weil's constant by `Iff.rfl`; axioms); `Discharges.lean` (65 open, 1526 checked, the same 6 discharges as
the base: the leaf is not a bundle field yet, and `hL3` is general); `MainEdit.lean`.

**What remains:** the integrator's `Main.lean` edit replacing `hL3` by the `C_d` chain (gz-weil §5, now with four
leaves). `autofold.json` (field `jacobiLambdaDeriv`, no leaves) applies only after gz-weil's leaves are folded.
Report: `docs/research/jacobi-lambda.md`.
