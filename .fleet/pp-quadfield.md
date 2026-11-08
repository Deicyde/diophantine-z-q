# pp-quadfield report: plan step 3.2 and the residue bound of step 3.5

All code is in `ZInQKernel/Progressions/QuadField/` (root module `ZInQKernel/Progressions/QuadField.lean`,
imported from `ZInQKernel.lean`), namespace `ZInQ.Progressions`. Imports are Mathlib only.
There is no `sorry` and no axiom beyond `propext`, `Classical.choice`, `Quot.sound` (checked with
`#print axioms` on `dedekindZeta_residue_ge`). `lake build ZInQKernel` succeeds.

The field is `Qsqrt d := QuadraticAlgebra ℚ (d : ℚ) 0` (an `abbrev`; `ω ^ 2 = d`). Every result
assumes only `[Fact (¬ IsSquare (d : ℚ))]`. The instance `Qsqrt.fact_not_isSquare` derives that
`Fact` from `Fact (Squarefree d ∧ d ≠ 1)`, and the lemma `Qsqrt.not_isSquare_of_squarefree` derives
it from explicit hypotheses.

| plan item (docs/effective-dirichlet-plan.md) | Lean name | status |
|---|---|---|
| 3.2 item 1: field, number field | `Qsqrt`, `Qsqrt.instCharZero`, `Qsqrt.instNumberField` (the `Field` instance is Mathlib's) | proved |
| 3.2 item 1: degree 2 | `Qsqrt.finrank : Module.finrank ℚ (Qsqrt d) = 2` | proved |
| 3.2 item 2: discriminant | `Qsqrt.abs_discr_le : \|discr (Qsqrt d)\| ≤ 4 * \|d\|` | proved |
| 3.2 item 3: signature, d > 0 | `Qsqrt.nrRealPlaces_of_pos` (= 2), `Qsqrt.nrComplexPlaces_of_pos` (= 0), `Qsqrt.isTotallyReal` | proved |
| 3.2 item 3: signature, d < 0 | `Qsqrt.nrRealPlaces_of_neg` (= 0), `Qsqrt.nrComplexPlaces_of_neg` (= 1), `Qsqrt.isTotallyComplex` | proved |
| 3.2 item 4: torsion | `Qsqrt.torsionOrder_le_six`; general form `torsionOrder_le_six_of_finrank_eq_two` | proved |
| 3.2 item 5: regulator, d < 0 | `Qsqrt.regulator_of_neg : regulator (Qsqrt d) = 1` | proved |
| 3.2 item 5: regulator, d > 0 | `Qsqrt.regulator_ge_of_pos : Real.log ((1 + √5) / 2) ≤ regulator (Qsqrt d)` | proved |
| 3.5: residue bound | `dedekindZeta_residue_ge : Real.log ((1 + √5) / 2) / (6 * √\|(d : ℝ)\|) ≤ dedekindZeta_residue (Qsqrt d)` | proved |

## Changes to the statements

- **Hypothesis on d.** The task assumes `d` squarefree, `d ≠ 0`, `d ≠ 1`. All statements need only
  "`d` is not a square in ℚ", passed as a `Fact`. This is weaker than the task's hypotheses: the
  instance above derives it from squarefreeness.
- **Regulator.** The task asks for `d > 1`. The bound is proved for every `d > 0` that is not a
  square, which is the same condition, since `d = 1` is a square.
- **Constants.** The constants match the plan. In the real case the proof gives the stronger bound
  `res ≥ log((1+√5)/2) / (3√d)`; in the imaginary case it gives `π / (6√|d|)`. The delivered
  statement uses the uniform constant 6.
- **Name of the field.** The field is called `Qsqrt d` instead of `K d`, to avoid a one-letter global
  name in `ZInQ.Progressions`.

## Proof routes

- **Discriminant.** The basis `(1, ω)` has discriminant `4d` (`Qsqrt.discr_basis`, from
  `Qsqrt.trace_eq : Tr(x + y√d) = 2x`). Write it in the integral basis: the change-of-basis matrix
  has integer entries (`integralBasis_repr_apply`), so `4d = m² · disc K`
  (`Qsqrt.exists_four_mul_eq_sq_mul_discr`). Since `m ≠ 0`, this gives `|disc K| ≤ 4|d|`. The ring
  of integers is never computed.
- **Torsion.** The torsion group contains a primitive root of unity of order `w`. Then
  `IsPrimitiveRoot.lcm_totient_le_finrank` gives `φ(w) ≤ 2`. By induction over prime powers and
  coprime products, `φ(n) ≤ 2` implies `n ∣ 12` and hence `n ≤ 6`.
- **Regulator for d > 0.** There are two places, so the rank is 1. `regulator_eq_det` with a
  1×1 matrix gives `regulator = |log w(ε)|` for the fundamental unit `ε`, and `w(ε) ≠ 1` because the
  regulator is positive. For a unit, the trace `t` and the norm `n` are integers, by integrality of
  `x + x̄` and `x x̄`, and `n = ±1`. So under a real embedding, `y = ψ(ε)` satisfies
  `y² − t y + n = 0`. From this `|y| > 1` gives `|y| ≥ (1+√5)/2`: if `n = −1`, `|t| ≥ 1`; if
  `n = 1`, `|t| ≥ 3`. If `|y| < 1`, the same argument applies to `1/y`
  (`log_golden_le_abs_log`).
- **Regulator for d < 0.** The rank is 0, and the determinant of the empty matrix is 1.

## Lemmas added beyond the deliverables (all in `ZInQ.Progressions`)

`Qsqrt.not_isSquare_of_squarefree`, `Qsqrt.fact_not_isSquare` (instance), `Qsqrt.ringHom_apply`,
`Qsqrt.ringHom_omega_sq`, `Qsqrt.isTotallyReal`, `Qsqrt.isTotallyComplex`,
`dvd_twelve_of_totient_le_two`, `le_six_of_totient_le_two`, `torsionOrder_le_six_of_finrank_eq_two`,
`Qsqrt.isIntegral_omega`, `Qsqrt.trace_eq`, `Qsqrt.discr_basis`, `Qsqrt.ne_zero`,
`Qsqrt.sqrtInt` (`√d` in `𝓞 (Qsqrt d)`), `Qsqrt.coe_sqrtInt`, `Qsqrt.sqrtInt_sq` (`sqrtInt ^ 2 = d`),
`Qsqrt.exists_four_mul_eq_sq_mul_discr`, `golden_le_of_quadratic`, `log_golden_le_abs_log`,
`Qsqrt.exists_int_trace_norm`, `Qsqrt.unit_quadratic`, `log_golden_lt_one`, `log_golden_pos`.

## Problems

None. Mathlib's `QuadraticAlgebra` carries two `Algebra ℚ (Qsqrt d)` instances,
`QuadraticAlgebra.instAlgebra` and `DivisionRing.toRatAlgebra`. They agree up to implicit
arguments, and `rw` with `Qsqrt.finrank` worked in goals that came from NumberField lemmas.

## Suggestions for the next agent (pp-realbound)

- To use pp-idealcount's results, take `K := Qsqrt d`. Its hypotheses are supplied by
  `Qsqrt.finrank` and by the integral square root `Qsqrt.sqrtInt` with `Qsqrt.sqrtInt_sq`.
- Provide the field hypothesis either with `haveI : Fact (¬ IsSquare (d : ℚ)) :=
  ⟨Qsqrt.not_isSquare_of_squarefree hd h1⟩` or by putting `Fact (Squarefree d ∧ d ≠ 1)` in context.
- To get `res_K ≥ log((1+√5)/2) / (6√q)` from `|d| ≤ q`, combine `dedekindZeta_residue_ge` with
  `Real.sqrt_le_sqrt`.
