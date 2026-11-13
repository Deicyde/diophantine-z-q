# r1b-state results log

## Statements
- `R1bState.R1bProps Y Φ` (clauses (a) every `P : QML3 ℂ` has a QM-compatible uniformization by
  some `Λ_τ`, `τ ∈ ℍ`; (b) a family `y : ℍ → Y(ℂ)` with `Φ(y τ)` = class of an object
  uniformized by `Λ_τ` with the standard level structure; (c) regular functions are holomorphic
  along `y`), `R01b_ComplexUniformization' := ∃ Y Φ, R1fpProps Y Φ ∧ R1bProps Y Φ`.

## Compile outcomes
- run1 (06:37): build of Analytic.Uniformization, QMLattice, QM.Pin, LeafPush2.R22: OK (3m48s).
- run2: errors (`*ᵥ` notation needs `open Matrix`; `MonObj` opens for the group on points;
  `rw` with `specToEquivOfField_comp_right` fails on `(fieldPt ℂ).left` vs `Spec ℂ`).
- run3: fixed by scheme-level `ptOfS`, `evalS`; one `No goals` error.
