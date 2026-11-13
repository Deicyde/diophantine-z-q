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
- run9 (06:50): `lake build ZInQKernel.Hypotheses.JHeight ZInQKernel.HDecomp.Assembly` (upstream
  `ZInQ` helpers needed by `Assembly`): OK.
- run10-14: Part3_Fibre (FibreQMPeriod reduction) and Part4_Probes fixed; run15 (06:55): R1b.lean
  = PkgI1Copy + R1b + Part2_P1 + Part3_Fibre + Part4_Probes + Part9_Audit: **0 errors, no
  `sorry`**; `#print axioms` of `r1bProps_of_leaf`, `R1bProps.of_hom`,
  `holomorphicP1On_of_family`, `q3_form_of_R1bProps`, `fibreQMPeriod_of_r1b`, `iotaC_mem`,
  `level_ker`, `level_linear`, `iota_mul`: `[propext, Classical.choice, Quot.sound]` (VERIFIED).

## Findings
- `FibreQMPeriod'` (g0-thetapoint's `FibreQMPeriod`, build names) follows from
  `R01b_ComplexUniformization'` + `PkgI1.QMHauptmodul` + glue `HauptmodulCompare` + glue
  `UnifBaseChange` (`fibreQMPeriod_of_r1b`, VERIFIED compiled). No `PinUnique`/`MobiusGlue`
  needed: `phi_part` maps the leaf's witness to any candidate, and `R1bProps` transports forward.
- Consistency probes (VERIFIED compiled): `ι(a)Λ_τ ⊆ Λ_τ` for `a ∈ 𝒪` (`iotaC_mem`); `ι`
  multiplicative (`iota_mul`); the level map `a ↦ [ι(a)(τ,1)ᵀ/3]` is `𝒪`-linear with kernel
  exactly `3𝒪` (`level_linear`, `level_ker`), matching `Level3`'s convention
  `η(ab) = ι(a)η(b)`. So neither compatibility clause is inconsistent on the torus side.
- In the build, `ZInQ.DefFaltings` uses `PkgI3.AbVar` itself (`Faltings/Models.lean`:
  `open PkgI3 (AbVar)`), so `LeafAdopt.abVarEquiv` is the identity there (VERIFIED, read).
