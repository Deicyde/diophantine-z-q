# `ParametrizationPeriodsGlue` (G1): PROVED

This directory proves the named step `ParametrizationPeriodsGlue` (G1) of the reduction of
`NewformPeriodsRational` in `ZInQKernel/Contrib/RC53Assist/NewformPeriods/` (`Glue.lean`,
lines 68–73). The statement is used unchanged; nothing is assumed: no hypothesis, no print, no
named step. `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for every theorem in
the file.

## File

| File | Content | Status |
|---|---|---|
| `ParametrizationPeriods.lean` | `ParametrizationPeriodsGlue`, its analytic core, the `q`-expansion calculus, `ℚ(j, j_M)` as functions on `ℍ` | PROVED |

Everything is in one file because it is checked as a single file against built modules
(`lake env lean ZInQKernel/Contrib/RC53Assist/NewformPeriodsG1/ParametrizationPeriods.lean` from
the repository root). It imports only `ZInQKernel.Contrib.RC53Assist.NewformPeriods.Reduction`
and two Mathlib modules. It is not yet imported by any library root.

## Main theorems (namespace `ZInQ.Contrib.RC53Assist.NewformPeriodsG1`)

```lean
theorem parametrizationPeriodsGlue_holds : ParametrizationPeriodsGlue

theorem newformPeriodsRational_of_prints_G0_G2
    (hS : Shimura1973Thm1RationalGamma0) (hF : Faltings1983Kor2EllipticQ)
    (h0 : NewformOfModularCurveGlue) (h2 : IsogenyLatticeGlue) :
    ZInQ.Contrib.CloudB3RC53.ModularWeil.NewformPeriodsRational
```

The second theorem is `newformPeriodsRational_of_prints` with `G1` discharged.

Intermediate results:

* `isParamScale_of_local_curve_point` (analytic core). Let `g ∈ S₂(Γ₀(M))`, `L` a lattice,
  `c ≠ 0`, and `X, Y : ℂ → ℂ`, where `X` is meromorphic and `Γ₀(M)`-invariant on
  `{Im τ > 0}`. Suppose that near one point `τ₀` with `Im τ₀ > 0` we have
  `Y² = X³ − (g₂/4) X − g₃/4` and `X' = 2πi c g · 2Y`, that `Y` is continuous at `τ₀`, and that
  `Y(τ₀) ≠ 0` and `g(τ₀) ≠ 0`. Then `IsParamScale M g L c`.
* `exists_notMem_weierstrassP_eq`: `℘` takes every complex value off the lattice.
* `mem_lattice_of_eventually_weierstrassP_add`: if `℘(z + ω) = ℘(z)` on a punctured
  neighbourhood of a point, then `ω` is in the lattice.
* `eventually_weierstrassP_comp_eq`: local lift through `℘` (inverse function theorem).
* `HasQExpansionAbove h H R`: `H(τ) = Σ_{n ∈ ℤ} hₙ e^{2πinτ}` for `Im τ > R`. Its calculus:
  `.add`, `.mul` (Cauchy product), `.inv` (reciprocals), `.hasDerivAt` (termwise derivative,
  `θ ↔ (2πi)⁻¹ d/dτ`), `.eq_zero` (uniqueness), `hasQExpansionAbove_cuspForm`,
  `hasQExpansionAbove_comp_mul` (`τ ↦ Mτ` is `qPow M`).
* `exists_jFunction`: `j = 1728 E₄³ (E₄³ − E₆²)⁻¹`, built from Mathlib's normalized Eisenstein
  series, is meromorphic and `SL₂(ℤ)`-invariant on `ℍ`, and its Laurent expansion is
  `jInvariantQ`. The coefficients of `E₄` and `E₆` are `240 σ₃(n)` and `−504 σ₅(n)`
  (`B₄ = −1/30`, `B₆ = 1/42`).
* `comp_mul_invariant`: `τ ↦ j(Mτ)` is `Γ₀(M)`-invariant (`M · γτ = γ'(Mτ)`).
* `modularFunctionQExpansion`: every element of `ℚ(j, j_M)` (`modularFunctionFieldQ M`) is the
  Laurent `q`-expansion of a `Γ₀(M)`-invariant meromorphic function on the upper half plane.
* `parametrizationPeriodsGlue_of_qExpansion`: `G1` from that statement.

## Proof outline

1. `x` and `y` become `Γ₀(M)`-invariant meromorphic functions `X`, `Y` on `ℍ` with Laurent
   expansions `x` and `y` near `∞`. The formal identities of `IsModularPointQ` and
   `PullbackIsMultiple` become identities of functions there:
   `X' = 2πi c g (2Y + a₁X + a₃)`, and `(X, Y)` lies on `A`.
2. Since `x` is not constant, `X'(τ₀) ≠ 0` at some `τ₀` near `∞` (uniqueness of expansions).
   Hence `g(τ₀) ≠ 0` and `2Y(τ₀) + a₁X(τ₀) + a₃ ≠ 0`.
3. In the coordinates `X + b₂/12` and `(2Y + a₁X + a₃)/2` the point lies on
   `Y² = X³ − (g₂/4) X − g₃/4`, because `g₂ = c₄/12` and `g₃ = c₆/216`.
4. Choose `z₀` with `℘(z₀) = X(τ₀) + b₂/12` and `℘'(z₀) = 2Y(τ₀) + a₁X(τ₀) + a₃`. Then
   `u = c F_g + (z₀ − c F_g(τ₀))` satisfies `℘ ∘ u = X + b₂/12` near `τ₀`: by the inverse
   function theorem, `u` and the local lift have the same derivative `2πi c g`.
5. By the identity theorem for meromorphic functions on the connected `ℍ`, this equality holds
   near every point of `ℍ`. For `γ ∈ Γ₀(M)`, the period `ω = c (F_g(γτ) − F_g(τ))` does not
   depend on `τ`, and the invariance of `X` gives `℘(z + ω) = ℘(z)` near `z₀`. Therefore
   `ω ∈ Lat`.

The vendored uniformization theorem `ℂ/Λ ≅ E(ℂ)` and the covering-space lifting are not needed:
step 4 uses only the surjectivity of `℘`, and step 5 uses only the fact that the poles of `℘` are
the lattice points.

## What remains

Nothing remains for `G1`. The reduction of `NewformPeriodsRational` still has the printed leaves
(Shimura 1973, Theorem 1; Faltings 1983, Korollar 2) with their consequence translations, plus
`G0` and `G2`. The table and the "Remaining formalization obligations" list in
`../NewformPeriods/README.md` still describe `G1` as GLUE and were left unchanged.
