# Task mult-formal-log: report

The two sorries `formalLog_formalAdd` and `ellLog_add` are now proofs.
`ZInQKernel/Multiplication/Local/FormalLogarithm.lean` has no sorry left. The only changes to that
file are the two proofs and one new import line (`ZInQKernel.Multiplication.FormalLog.LogAdd`).
Everything that depends on them is now axiom-clean (`propext`, `Classical.choice`, `Quot.sound`
only), checked with `#print axioms`: `ellLog_add`, `ellLog_zsmul`, `ellLog_injOn`,
`val_z_zsmul_eq`, `ellLog_unramified` and `ellLog_ratio`.

The statement of `formalGroupLaw_exists` is proved, under the name `formalGroupLaw_exists'`
(`FormalLog/GroupLaw.lean`). The sorry'd copy in `Local/FormalGroupLaw.lean` stays as it is:
see Problems.

`lake build ZInQKernel` succeeds. No `axiom`, `native_decide` or new options were added, and there
is no `sorry` in this task's files.

## Leaves

| article path | Lean name | status |
|---|---|---|
| multiplication/local/formal-logarithm.md (part 1) | `ZInQ.Mult.formalLog_formalAdd` (proof: `formalLog_formalAdd_aux`, FormalLog/Identity.lean) | proved |
| multiplication/local/formal-logarithm.md (part 2) | `ZInQ.Mult.ellLog_add` (proof: `evalLog_zCoord_add`, FormalLog/LogAdd.lean) | proved |
| multiplication/local/formal-group-law.md (part 2) | `ZInQ.Mult.formalGroupLaw_exists` (Local/FormalGroupLaw.lean) | statement only (sorry); the identical statement is proved as `ZInQ.Mult.formalGroupLaw_exists'` (FormalLog/GroupLaw.lean) |
| multiplication/local/formal-group-law.md (evaluation) | `ZInQ.Mult.hasSum_formalAdd` (FormalLog/ChordEval.lean): `z(P+Q) = F(z(P), z(Q))` | proved |
| multiplication/local/logarithm-isometry.md | `evalLog_isometry`, `ellLog_injOn`, `val_z_zsmul_eq` (mult-local's) | proved (now sorry-free through `ellLog_add`) |
| multiplication/local/logarithm-ratio.md | `ellLog_ratio` (mult-local's) | proved (now sorry-free) |

## Statement corrections

None. All three statements were formalized as written. Two notes:
- The blueprint has `A ∈ 𝒪 \ {0}`. The Lean statements allow `A = 0` as well, which is harmless.
- `ellLog_add` assumes `ResidueChar K p e`. Characteristic 0 follows from it
  (`ResidueChar.charZero`).

## Proof outline and lemmas added (all in `ZInQKernel/Multiplication/FormalLog/`)

- `Algebra.lean`: chord identities in an abstract commutative ring. These are `chordQ_of_roots`,
  `chord_third_root`, `chord_slope_deriv` and `chord_invariance`; the first and third cancel
  `a - b` once in a domain. The `linear_combination` coefficients were found with sympy. The
  scripts are not in the repository.
  - In the coordinates `(z, ω)` the curve is `ω = z³ + A z ω²`. The line `ω = λz + ν` meets it
    in the cubic `c(z) = (1+Aλ²)z³ + 2Aλν z² + (Aν²-λ)z - ν`.
  - Its third root is `-F`, so `ω(F) = λF - ν`.
  - Invariance of the differential: `∂₁F (1 - 2A T₁ ω(T₁)) = 1 - 2A F ω(F)`.
- `ChainRule.lean`: `pderiv_subst`, the chain rule `∂ᵢ f(a) = f'(a) ∂ᵢa` for
  `PowerSeries.subst` into `MvPowerSeries`; Mathlib only has the one-variable case. Also
  `coeff_subst_congr` and `coeff_pow_eq_zero_of_degree_lt`.
- `InvDiff.lean`: `invDiffSeries_mul_omega`, `S (1 - 2A T ω) = 1`. It also holds a copy of
  LogSeries' `invDiffSeries_sq` (as `invDiffSeries_sq_aux`), because `Local/LogSeries.lean`
  imports `Local/FormalLogarithm.lean`. Also `derivative_formalLog_aux`.
- `Relations.lean`: the pieces `ω(T₂)` (`omegaSnd`) and `(1+Aλ²)⁻¹` (`chordInv`), with:
  - the curve equations `omegaFst_eq` and `omegaSnd_eq`;
  - `chordSlope_mul_sub`, `λ(T₂ - T₁) = ω₂ - ω₁`;
  - `chordInv_mul`, `formalAdd_eq` and `formalAdd_def`;
  - the derivative relations `pderiv_zero_chordSlope_mul` and
    `subst_derivative_omegaSeries_mul`.
- `Identity.lean`: `formalLog_formalAdd_aux`.
  - Both sides have constant coefficient 0 and equal partial derivatives (`pderiv.ext`).
  - The `∂₂` case is the `∂₁` chord algebra with `T₁ ↔ T₂` swapped; `λ` and `ν = ω₂ - λT₂` are
    symmetric.
- `Eval.lean`: evaluation of two-variable power series.
  - `MvIntegral`: coefficients in `𝒪`, with closure lemmas.
  - `ev2 t₁ t₂ f = Σ f_n t₁^{n₀} t₂^{n₁}`, convergent for `v(tᵢ) ≥ 1`.
  - `ev2` is additive and multiplicative (Cauchy product over the antidiagonals of `Fin 2 →₀ ℕ`).
  - Series in one variable evaluate to their one-variable sums (`hasSum_ev2_subst_X_zero`/`_one`).
  - The pieces of `formalAdd` are integral; `chordInv` by well-founded induction on
    `coeff_invOfUnit`.
- `ChordAlgebra.lean`: `zCoord_add_of_line`. If `ω = Λz + N` passes through `P₁, P₂` (and is the
  tangent when `P₁ = P₂`), then `z(P₁+P₂) = z₁ + z₂ + 2AΛN/(1+AΛ²)`. The proof uses Vieta via
  `vieta_shortCurve` and `sum_t_identity` from `Model/Descent/KernelReduction.lean`.
- `ChordEval.lean`:
  - `zCoord_add_eq_of_line` handles the cases `P = O`, `Q = O`, `P + Q = O` and the general
    case.
  - `hasSum_formalAdd` evaluates the relations at `(z(P), z(Q))`. The tangent case comes from
    evaluating `∂₁λ (T₂ - T₁) = λ - ω'(T₁)` at `t₁ = t₂`.
- `LogAdd.lean`: `evalLog_add_of_hasSum` and `evalLog_zCoord_add`.
  - The family `(r, n) ↦ c_r (F^r)_n t^n` vanishes for `r > n₀ + n₁` and has valuation
    `≥ n₀ + n₁ - e v_p(r)`, so it is summable on `ℕ × (Fin 2 →₀ ℕ)`.
  - `Summable.tsum_comm` then exchanges the sums.
  - Also `ResidueChar.charZero` and `vge_logCoeffA`.
- `GroupLaw.lean`: `formalGroupLaw_exists'`.
  - Over a field of characteristic 0, `f ↦ log f` is injective on series without constant term.
    This uses Mathlib's compositional inverse `PowerSeries.substInvOfIsUnit`
    (`subst_formalLog_injective`).
  - Associativity, commutativity and `F(T, -T) = 0` follow from
    `log F(a, b) = log a + log b` (`subst_formalLog_subst_formalAdd`) and `log(-T) = -log T`.
  - The identities pass to `𝒪 = Valued.integer K` because coefficientwise mapping is injective
    and commutes with substitution (`map_formalAdd`, `map_subst_pair`).

## Problems

- `formalGroupLaw_exists` sits in `Local/FormalGroupLaw.lean`, which defines `formalAdd` and is
  imported by all of this task's modules. Its sorry therefore cannot be replaced by a call to a
  lemma in this directory without an import cycle. `formalGroupLaw_exists'` has exactly the same
  statement, and nothing uses the sorry'd declaration.
  Suggestion: delete `formalGroupLaw_exists` from `Local/FormalGroupLaw.lean` and rename
  `formalGroupLaw_exists'` to it, or point the blueprint's `lean:` field at
  `ZInQ.Mult.formalGroupLaw_exists'`.
- My files compile with `if_pos`/`if_neg` deprecation warnings, as other modules do. I made no
  other changes outside my directory.

## Suggestions for the next agent

- `ev2`, `MvIntegral` and the interchange argument in `LogAdd.lean` are general. They can be
  reused for other evaluations of two-variable integral series on `𝔪 × 𝔪`, and the lemmas take
  any complete `ℤᵐ⁰`-valued field.
- The `invDiffSeries_sq` duplication would disappear if `invDiffSeries_sq` and
  `invDiffSeries_mul` moved from `Local/LogSeries.lean` to a module that does not import
  `Local/FormalLogarithm.lean`.
