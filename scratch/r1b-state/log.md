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
- run4-8: `ptOfS` made an `abbrev` (residue-field types must match reducibly); `π`-form
  proof adjusted (`refine (val_of_mem …).trans ?_`, `show`). Clean: R1b.lean (PkgI1Copy +
  R1b.part + Part2_P1.part) compiles with no error, no `sorry` (deprecation warnings only).
  Proved: `R1bProps.of_hom`, `r1bProps_of_leaf` (the ∃-leaf gives R1bProps for every
  `(Y, Φ)` with `R1fpProps`), `holomorphicP1On_of_family`, `q3_form_of_R1bProps`.
