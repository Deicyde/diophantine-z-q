# assembly-real report

Task: the real-place analysis of the assembly chapter (blueprint `assembly/approximation/`).
Root module `ZInQKernel/Assembly/Real.lean` (imported from `ZInQKernel.lean`); modules
`ZInQKernel/Assembly/Real/{Subtraction,Accumulation,Derivative}.lean`, namespace `ZInQ.Assembly`.
All three leaves are proved. There is no `sorry`, `native_decide` or axiom in these modules, and no
finite computation. `#print axioms` on the four main theorems gives only
`propext, Classical.choice, Quot.sound`. `lake build ZInQKernel` succeeds. The only `sorry`
warning in the build is the existing one in `ZInQKernel/Main.lean`.

## Status

| article | Lean name(s) | status |
| --- | --- | --- |
| assembly/approximation/real-subtraction.md | `Assembly.realCurve`, `Assembly.RealCurve.TendstoPt`, `RealCurve.exists_subseq_tendstoPt` (part 1), `RealCurve.tendstoPt_sub_zero` (part 2) (Subtraction.lean) | proved |
| assembly/approximation/real-accumulation.md | `Assembly.exists_multiple_large` (Accumulation.lean) | proved, with hypothesis `¬ IsOfFinAddOrder genP0` |
| assembly/approximation/real-derivative.md | `Assembly.zCoord`, `Assembly.z_ratio_tendsto` (Derivative.lean) | proved |

## Statements and differences from the articles

- **real-subtraction.** `realCurve e := shortCurve (-e ^ 2)` (model-field's short Weierstrass
  curve, so `y² = x³ - e²x`). `TendstoPt P Q` is defined for any `W : WeierstrassCurve ℝ` using the
  coordinate functions `ptX`, `ptY`, which return `0` at `O`:
  `TendstoPt P 0 ↔ ∀ M, ∀ᶠ m in atTop, P m = 0 ∨ M < ptX (P m)`, and for affine `Q = (x₀, y₀)`,
  `(∀ᶠ m, P m ≠ 0) ∧ ptX ∘ P → x₀ ∧ ptY ∘ P → y₀`. This is the article's definition word for
  word: in the `O` case, `M < ptX (P m)` with `P m ≠ 0` means "affine with `x > M`". Part 1:
  `∃ φ, StrictMono φ ∧ ∃ Q, TendstoPt (P ∘ φ) Q`. Part 2:
  `TendstoPt P Q → TendstoPt P' Q → TendstoPt (fun m => P' m - P m) 0`. Both assume `e ≠ 0`.
  The proof follows the sketch: chord and tangent cases with a slope `ℓ` satisfying `ℓ·D = N`,
  where `N → c ≠ 0` and `D → 0`; the case `Q = O` translates by `T = (0, 0)`.
- **real-accumulation.** `σ₊`, `σ₋` are model-field's `K0.embPlus` and `K0.embMinus`
  (`ZInQKernel/Model/Field/Basic.lean`, `s ↦ ±√2`), which were already on main, so no local copies
  were defined. Statement:
  `exists_multiple_large (hP0 : ¬ IsOfFinAddOrder genP0) (M : ℝ) : ∃ k : ℕ, 1 ≤ k ∧ ∃ x y h,
  (k : ℤ) • genP0 = .some x y h ∧ M < K0.embPlus x ∧ M < K0.embMinus x`.
  **The infinite order of `P₀` is an explicit hypothesis.** On `origin/wip/model-descent` there is
  still no statement of the form `¬ IsOfFinAddOrder genP0`. The part that does not need it,
  `exists_nsmul_near_zero` (`σ±([k]P₀)` is `O` or has abscissa `> M`), has no hypothesis.
- **real-derivative.** `zCoord : genCurve.toAffine.Point → K0` is `z = -x/y`, with value `0` at `O`.
  This is a local definition; the lead can identify it with the shared `z` of
  `precision-predicate.md`. `τ` is any ring homomorphism `K0 →+* ℝ`. This is more general than
  `τ ∈ {σ₊, σ₋}`, but those are the only two such homomorphisms. The statement is the
  implementation note's draft. The article is correct. The proof does not take the limits of
  `x([n]Q)/x` and `y([n]Q)/y` separately. It writes
  `z([n]Q)/z(Q) = Φ_n(x) ΨSq_n(x) / (x f_{2n}(x))` (`n ≥ 1`), one quotient with numerator and
  denominator of degree `2n² - 1` and leading coefficients `n²` and `n`. The nonvanishing of
  `Φ_n(τx)`, `ΨSq_n(τx)`, `τx` and `f_{2n}(τx)` for large `τx` follows from that quotient
  tending to `n ≠ 0`. Negative `n` comes from `z(-P) = -z(P)`.

## Lemmas added beyond the leaves

- Subtraction.lean: `RealCurve.ptX`, `ptY`, `eq_some_of_ne_zero`, `equation_iff`, `isElliptic`,
  `nonsingular_of_equation`, `sq_ptY`, `neg_abs_le_of_sq` (`x ≥ -|e|`), `deriv_ne_zero_of_root`,
  `sub_some_cases` (explicit `P' - P` on `y² = x³ + Ax` over `ℝ`), `eventually_lt_abs_of_mul_eq`,
  `lt_sq_of_lt_abs`, `tendstoPt_sub_zero_of_some`, `nonsingular_T`, `add_T_some`,
  `tendstoPt_add_T`, `tendstoPt_zero_iff`, `tendstoPt_some_iff`.
- Accumulation.lean: `shortCurve_map`, `nonsingular_mapShort`, `mapShortPt` (the group
  homomorphism `E_A(F) →+ E_B(K)` induced by a field homomorphism with `f A = B`, with
  `mapShortPt_zero` and `mapShortPt_some`), `RealCurve.TendstoPt.comp_strictMono`, `map_genA`,
  `map_genD_ne_zero`, `realPt σ : genCurve.toAffine.Point →+ (realCurve (σ genD)).toAffine.Point`,
  `realPt_some`, `exists_nsmul_near_zero`.
- Derivative.lean: `psiEval_natCast`, `psiEval_sq` (`ψ_k² = ΨSq_k(x)`), `psiEval_phi`
  (`xψ_{m+1}² - ψ_{m+2}ψ_m = Φ_{m+1}(x)`), `psiEval_double` (`ψ_{2k} = 2y f_{2k}(x)`), all for
  `y² = x³ + Ax` over any commutative ring; `zNum`, `zDen`, with `natDegree`, `degree` and
  `leadingCoeff` lemmas; `genCurve_sq_genA`; `z_ratio_tendsto_succ` (the case `n = m + 1`).

## Problems

None open. Mathlib has no topology on elliptic-curve points, so `TendstoPt` replaces it as the
article intends.

## Suggestions for the next agent

- Removing the hypothesis `hP0`: `origin/wip/model-descent` has
  `isOfFinAddOrder_iff_two_nsmul_eq_zero` (Torsion.lean). Together with model-field's
  `shortCurve_two_nsmul_some_eq_zero_iff` and `genY0_ne_zero` it gives `¬ IsOfFinAddOrder genP0`
  in a few lines. Once that is on main, discharge `hP0` in `exists_multiple_large` (and in
  `iota_eq_psi`).
- close-completeness can use `exists_multiple_large` with `M` from `z_ratio_tendsto` for both
  `τ = K0.embPlus` and `τ = K0.embMinus`. `realPt` and `mapShortPt` are available if a
  statement about the embedded points themselves is needed.
- When `precision-predicate.md` is formalized, identify its `z` with `Assembly.zCoord`, or
  restate `z_ratio_tendsto` with the shared name.
