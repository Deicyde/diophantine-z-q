# Report: division-polys

Branch `wip/division-polys`. Directory `ZInQKernel/Model/DivisionPolynomials/`, root module
`ZInQKernel/Model/DivisionPolynomials.lean` (imported from `ZInQKernel.lean`). `lake build ZInQKernel`
succeeds. No `sorry`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound` (checked with
`#print axioms` on the main theorems). No `native_decide`, and no constants are ever evaluated.

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| `syntax/division-polynomials.md` | `ZInQ.Syntax.normDiv`, `ZInQ.Syntax.divPsi`, `ZInQ.Syntax.psiComponent` (plus `psiEval`, `ComponentRing`, `componentA`; recurrences `normDiv_zero`…`normDiv_four`, `normDiv_even`, `normDiv_odd`, `divPsi_neg`) | proved |
| `syntax/division-polynomials-classical.md` | `ZInQ.Syntax.normDiv_eq_preΨ'`, `ZInQ.Syntax.divPsi_eq_Ψ`, `ZInQ.Syntax.mk_divPsi`, `ZInQ.Syntax.psiEval_eq_evalEval_ψ` (curve `ZInQ.Syntax.WA A`) | proved |
| `syntax/division-polynomial-multiplication.md` | `ZInQ.DivisionPolynomialMultiplication : Prop` (def), `ZInQ.divisionPolynomialMultiplication : DivisionPolynomialMultiplication` (theorem) | proved |
| `model/field/division-polynomial-multiples.md` | `ZInQ.mulByN_formulas : DivisionPolynomialMultiplication` (E over K₀), `ZInQ.mulByN_formulas_of_charZero` (any field of characteristic 0, any `A`); core theorem `ZInQ.DivisionPolynomials.zsmul_spec` | proved |
| `model/field/fixed-point-codes.md` | `ZInQ.iota_eq_psi` (under hypothesis `¬ IsOfFinAddOrder genP0`), `ZInQ.iota_eq_psi_of_ne_zero` (needs only `n • genP0 ≠ 0`); `ZInQ.psiP0`, `ZInQ.fixedX`, `ZInQ.fixedY` | proved, statement has an extra hypothesis (see below) |

## Statement corrections and choices

1. **`normDiv`** is defined as Mathlib's `preNormEDS' D₀ f₃ f₄` with `D₀ = 16(x³+Ax)²`, `f₃`, `f₄` as in the
   article (`divD0`, `divF3`, `divF4`). Mathlib's recursion is the article's recursion verbatim; the lemmas
   `normDiv_even` (m ≥ 3) and `normDiv_odd` (m ≥ 2, with the `D₀L - R_m` / `L - D₀R_m` case split) state
   it in the article's form. `divPsi A n = sign(n) · C(f_|n|) · (2Y if n even else 1)` in `R[X][Y]`;
   `psiEval A n x y` is its value.
2. **Components.** `psiComponent n c` is the `s^c` coefficient of `ψ_n(⟨X0,X1⟩, ⟨X2,X3⟩)` in
   `QuadraticAlgebra (MvPolynomial (Fin 4) ℤ) 2 0` with `A = ⟨-11243, 7950⟩`. The syntax constructor
   `psi e (a₀,…,a₃) c` is **not** defined here (it belongs to the syntax AST, owned by syntax-language);
   its semantics is given by the added bridge `ZInQ.Syntax.psiComponent_eval`:
   `eval v (Ψ_{n,c}) = c-th component of ψ_n(v₀ + v₁s, v₂ + v₃s)` in K₀ with `A = genA = -d²`.
3. **Classical agreement.** The final assertion ("agrees modulo the curve equation") is formalized as
   `mk_divPsi` (equality in `CoordinateRing`) and `psiEval_eq_evalEval_ψ` (equal values at every point).
4. **Multiplication formulas.** The theorem needs no `A ≠ 0`, and holds at every nonsingular affine point
   for every `n ∈ ℤ` (for `n = 0` both parts are trivial). Characteristic 0 is used only to know `ψ_n ≠ 0`
   in the function field (leading coefficient `n` or `n/2`) and that `2 ≠ 0`. The proposition
   `DivisionPolynomialMultiplication` keeps the article's `n ≠ 0` and its part-2 premise `[n]P ≠ O`.
   `genA := -genD ^ 2`, with `genA_eq : genA = ⟨-11243, 7950⟩` and `genCurve_eq_WA : genCurve = WA genA`
   (both `rfl`-level).
5. **Fixed point codes.** The proof needs Proposition 3.1's torsion part (P₀ has infinite order), which
   is not formalized yet; the implementation notes give its future name as
   `ZInQ.genP0_not_isOfFinAddOrder`. `iota_eq_psi` takes `¬ IsOfFinAddOrder genP0` as a hypothesis and
   proves the rest of the article: for `n ≥ 1`, `ψ_n(P₀) ≠ 0`, `ι(n)` is the code built from `fixedX n`,
   `fixedY n`, `ι(-n)` is the same with the last two coordinates negated, and `ι(0) = (1,0,0,0,0)`.
   Once the torsion theorem exists, `iota_eq_psi genP0_not_isOfFinAddOrder` is the unconditional statement.
6. **Proof route for the multiplication theorem** (differs from the article's sketch, which uses divisors
   and pole orders):
   - *Phase A* (`NonTorsion.lean`, `Algebra.lean`, `Geometry.lean`): at a point where `ψ_k(P) ≠ 0` for all
     `k ≠ 0`, compute `x([n]P)` by double-and-add strong induction. The recurrences for `ψ_{2m}`, `ψ_{2m±1}`
     are exactly relations between differences of abscissas (`dE_rel`, `dO_rel`, `dx_rel`). The induction
     step reduces to two 3-variable identities derived from the chord sum/product formulas: the even one
     holds identically, the odd one modulo the relation tying `x(U)`, `x(V)`, `x(U−V)`. The certificates
     were found with sympy and are checked by `linear_combination`. The ordinate follows from
     `x(Q+P) − x(Q−P) = −4y(Q)y(P)/(x(Q)−x(P))²`.
   - *Phase B* (`Jacobian.lean`, `Generic.lean`): with `jac n = (4φ_n, 4c_n, 2ψ_n)` (`c_n` = Mathlib's
     `complEDS₂` = `2ω_n`), Phase A at the generic point of the curve (in `FunctionField`, where
     `ψ_n ≠ 0` by `preΨ'_ne_zero`) gives `dblXYZ (jac n) = 8 • jac (2n)` and
     `addXYZ (jac (n+1)) (jac n) = (−8) • jac (2n+1)`. These identities are pulled back to the coordinate
     ring and evaluated at any point (`jac_identities`).
   - *Phase C* (`Multiples.lean`): at any point, double-and-add with Mathlib's Jacobian group law
     (`add_self`, `add_of_not_equiv`, `toAffine_add`, `nonsingular_add`) shows `jac n` represents `[n]P`.
     There is **no torsion case split**, because Mathlib's formulas are valid for all nonsingular
     representatives (including `O`); `Z = 2ψ_n` gives part 1 and the affine coordinates give part 2.

## Lemmas added beyond the leaves

- `Geometry.lean`: `WA_equation_iff`, `WA_negY`, `WA_add_X`, `exists_add_of_X_ne`, `exists_add_self_of_Y_ne`,
  `chord_rel` (sum, product, difference of `x(Q±R)`), `dbl_rel`.
- `Algebra.lean`: `even_step_alg`, `odd_step_alg`, `base2_alg`, `base3_alg`, `y_alg` (pure field identities).
- `NonTorsion.lean`: `w` (values of ψ as Mathlib's `normEDS`, any commutative ring), `xmul`, `ymul`,
  `w_zero`…`w_four`, `w_neg`, `w_even`, `w_odd`, `dx_rel`, `dE_rel`, `dO_rel`, `nsmul_sub_one`,
  `exists_nsmul_eq_xmul`, `exists_nsmul_eq`.
- `Jacobian.lean`: `cw`, `phiw`, `jac`, `w_mul_cw`, `WA_map`, `map_w`, `map_cw`, `map_jac`, `addZ_jac`,
  `dblZ_jac`, `jac_div_X`, `jac_div_Y`, `jac_Z`, `eq_of_toAffine_eq`, `jac_spec_of_ne_zero`,
  `jac_identities_of_ne_zero`.
- `Generic.lean`: `map_smul_fin3`, `φC`, `gx`, `gy`, `gA`, `g_eq`, `gy_ne_zero`, `CR_two_ne_zero`,
  `w_generic`, `w_generic_ne_zero`, `eq_of_map_eq`, `evalEval_gx/gy/gA`, `jac_identities_generic`,
  `jac_identities`.
- `Multiples.lean`: `psiEval_eq_w`, `jac_zero`, `jac_one`, `jac_spec`, `nsmul_spec`, `zsmul_spec`.
- `MulByN.lean`: `genA`, `genA_eq`, `genCurve_eq_WA`.
- `Components.lean`: `normDiv_eval`, `map_psiEval`, `componentEval`, `componentEval_componentA`,
  `psiComponent_eval`.

## Problems

- **Push blocked.** `git push origin HEAD:wip/division-polys` fails: there is no direct connection to
  github.com, and via `fwdproxy:8080` the CONNECT is refused with 403. `git fetch` fails the same way. All
  work is committed locally on `wip/division-polys` in the shared repository; the lead must push it from a
  machine with GitHub access.
- **origin/main.** Because fetch is blocked, I merged the local `origin/main` ref (at `1578910`, which
  already contains model-field's `Codes.lean` with `genP0`, `pointCode`, `iota`). The only conflict was
  `ZInQKernel.lean` (import lines; both kept).
- **Fixed point codes** depend on P₀ having infinite order (not yet formalized), see correction 5.

## Suggestions for the next agent

- When `genP0_not_isOfFinAddOrder` lands, add `iota_eq_psi genP0_not_isOfFinAddOrder` as the
  unconditional leaf.
- `DivisionPolynomialMultiplication` is a theorem now; it must not become an extra hypothesis
  (`ZInQKernel/Hypotheses/DivisionPolynomial.lean` from the notes is unnecessary).
- Two names exist for the same curve: `ZInQ.Syntax.WA A` (here) and model-field's `ZInQ.shortCurve A`.
  Both are `rfl`-equal to `genCurve` at `A = -genD²`; a later cleanup could keep one.
- The fixed-scalar semantics can use `psiComponent_eval` (rational evaluation of `Ψ_{n,c}`) together with
  `mulByN_formulas`. For the identity `ψ_{2n} = 2ψ_nω_n`, use `w_mul_cw` with `ω_n = cw/2`; to pass between
  `psiEval` and `w` on the curve, use `psiEval_eq_w`.
- Phase A/B/C work verbatim for `y² = x³ + Ax + B` with more chord algebra if a general short-Weierstrass
  version is ever needed; Phase C is curve-independent once the two Jacobian identities are known.
