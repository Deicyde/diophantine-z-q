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

## Numerical check (`jden_check.py`, output `jden_check_out.txt`; mpmath 30 digits, N = 18)
- disc −3 point `τ = i√3` (fixed point of `ι((1+j)/2)`): `|Σθ⁸| ≈ 6e-30`, `|∏θ| ≈ 1e-31`: jDen = 0
  AND jNum = 0, so Lean's `jNum/jDen = 0` there while `π = ∞` (the x/0 trap is real; VERIFIED
  numerically).
- disc −4 point `τ = √2 + i`: `|Σθ⁸| = 33.9`, `|∏θ| ≈ 1e-30`: jDen ≠ 0, `jNum/jDen ≈ 0 = π`.
- disc −24 point `τ = 4.1815…i`: `jNum/jDen = −0.592592… = −16/27`.
- five sample points (incl. the u = 1 fibre point `τ_u ≈ 1.3933 + 0.8693i`, where
  `jNum/jDen = −0.0040860 = J(1)`): `|Σθ⁸|` between 7.7 and 108, nonzero.
- So at both elliptic CM points −3, −4 the type-μ polarization of `Ω(τ)` has `∏θ = 0`
  (a product polarization), as the review's trap says.
- run17-18 (07:0x): Part5_Split: `HauptmodulCompare` from `FamilyHauptmodul` (the only piece
  using R1(b)'s family clauses), `PiOfQMLattice`, `JDenNonzero` (`hauptmodulCompare_of_parts`),
  and `fibreQMPeriod_of_r1b_parts`. One rename (`γ` is a token under the opens; bound variable
  renamed `g`). Clean, 0 errors; both new theorems `[propext, Classical.choice, Quot.sound]`.
