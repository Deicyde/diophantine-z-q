# pole-switch: Route K pole polynomial (`x + 3ℓ` → `x + ℓ`)

The pole polynomial is now the Route K one: `T₁ = A(A - e)(A + e)`, `T₂ = A(Az² - eH)(Az² + eH)`.
Its two curves are the congruent number curves `y² = x(x - ℓ)(x + ℓ)`, for `ℓ = e` and `ℓ = eH`.
The full build `lake build ZInQKernel` succeeds with no `sorry`, and `python3 scripts/check_target.py` passes.
`#print axioms ZInQ.exists_bounded_integer_polynomial_defining_integers_of` lists only
`[propext, Classical.choice, Quot.sound]`. `ZInQ.Assembly.poleSoluble_no_negative_odd` and
`ZInQ.Mult.pole_obstruction` give the same output.

## Status

| article path | Lean name | status |
| --- | --- | --- |
| (definition) `hypotheses` / pole polynomial | `ZInQ.polePoly` | changed to Route K |
| (definition) template polynomial | `ZInQ.Syntax.poleT1`, `ZInQ.Syntax.poleT2` (hence `polePolyOf`, `polePolyX`, `poleTemplate`) | changed to Route K |
| (definition) pole witness system | `ZInQ.Mult.poleSystem` | new (Route K copy of upstream's `ValuationObstruction.poleSystem`) |
| `multiplication/abscissa-parity.md` | `ZInQ.Mult.abscissa_val_even` | proved; **statement changed** (see below) |
| `multiplication/pole-obstruction.md` | `ZInQ.Mult.pole_obstruction`, `ZInQ.Assembly.poleSoluble_no_negative_odd` | proved, statements unchanged |
| hypothesis PC | `ZInQ.PoleCompleteness` | statement text unchanged; it now refers to the Route K `polePoly` |

## Files changed and why

- `ZInQKernel/Hypotheses/Pole.lean`
  - `polePoly`: `A + 3 * e` became `A + e`, and `A * z ^ 2 + 3 * e * H` became `A * z ^ 2 + e * H`.
  - The docstrings of the module, `polePoly`, `PoleSoluble` and `PoleCompleteness` now say that
    this is the Route K polynomial (curve `x + ℓ`) and that the manuscript's `Q_pole` uses `x + 3ℓ`.
- `ZInQKernel/Syntax/Templates/Core.lean`: the same change in `poleT1` and `poleT2`, and in
  their docstrings and the docstring of `polePolyOf`.
  - `ev_polePolyX`, `poleBuild_run`, `poleTemplate_params`, `poleTemplate_witnesses`,
    `poleTemplate_wf`, `poleTemplate_poly` and `poleTemplate_rel_iff` re-check without edits.
- `ZInQKernel/Multiplication/Certificate/Parity.lean`
  - Upstream `lean/ZInQ/PoleValuation.lean` is frozen and is about the `x + 3ℓ` system, so its
    curve-dependent parts are copied here with `3ℓ` replaced by `ℓ`:
    - the new definition `ZInQ.Mult.poleSystem`;
    - the new lemma `ZInQ.Mult.congruentCurve_rhs_nonzero_and_valuation`;
    - the new lemma `ZInQ.Mult.poleSystem_no_negative_odd_valuation`.
  - `abscissa_val_even` now covers the curve `x + l` and no longer needs `p ≠ 3`.
  - `poleSystem_of_polePoly_eq_zero` and `pole_obstruction` now use the local system. Their
    proofs and statements are unchanged.
  - Only the curve-independent upstream lemmas are still imported, through a selective `open`:
    `PoleWitness`, `poleMultiplier`, `poleA`, `poleH`,
    `poleMultiplier_nonzero_and_valuation_zero` and `negative_input_pole_h_valuation`.
- `ZInQKernel/Assembly/Local/PoleObstruction.lean`: `poleSoluble_no_negative_odd` now calls
  `Mult.poleSystem_no_negative_odd_valuation`. The `import ZInQ.PoleValuation` and the
  `open ZInQ.ValuationObstruction` are gone, and the docstring is updated. The statement is unchanged.

These files needed no edit and recompiled unchanged:
- `Assembly/Values/ValueTest.lean`: it uses only `poleTemplate_rel_iff`.
- `Size/Majorants/Templates.lean`: `poleTemplate_maj` is still proved by `size_maj`.
- `Syntax/Builder/Scope.lean`, `Syntax/Templates/{Certificate,Value,Library}.lean` and `Multiplication/Certificate/Slope.lean`.
- `Size/Majorants/TemplateHeights.lean`.

No kernel-checked table records coefficient data of the pole template. The variable count
292890231905 and the target bounds are untouched.

## Statement corrections

- `ZInQ.Mult.abscissa_val_even`, blueprint `multiplication/abscissa-parity.md`. It now reads:
  for a prime `p`, if `x, ℓ ≠ 0`, `v_p(ℓ)` is even and `y² = x(x - ℓ)(x + ℓ)`, then `v_p(x)` is even.
  - The old version had the curve `x + 3ℓ` and the hypothesis `p ≠ 3`.
  - The article needs the new curve and can drop `p ≠ 3`.
- `polePoly`, `PoleSoluble` and `PoleCompleteness`: the blueprint and manuscript text for
  `Q_pole`, Φ and PC should say `A + e` and `Az² + eH` (Route K).
  - Lemma 5.1 (pole obstruction) keeps its statement, and `S₀` is unchanged.

## Soundness proof outline (Lemma 5.1, Route K)

This follows `docs/research/rv-route-k.md` §4.1. Let `B ≠ 0`, take a solution of `poleSystem B v`,
and take a prime `p ∤ 2730` with `k = v_p(B) < 0` odd.

1. The multiplier `m` is a `p`-adic unit (upstream lemma). So `v(A) = k`, `H ≠ 0` and
   `v(H) = 3k` (upstream lemma).
2. The equation `eHzw = 1` gives `e, z ≠ 0`.
3. **Curve lemma** (`congruentCurve_rhs_nonzero_and_valuation`). Assume `x, l ≠ 0` and
   `v(x) ≠ v(l)`. Then:
   - `v(x - l) = v(x + l) = min(v x, v l)`, by the ultrametric equality case; this holds for every `p`;
   - `x(x - l)(x + l) ≠ 0`, with valuation `v(x) + 2 min(v x, v l)`.
4. **Parity** (`abscissa_val_even`). If `v(l)` is even:
   - when `v(x) = v(l)`, `v(x)` is even at once;
   - otherwise `2v(y) = v(x) + 2·min`, so `v(x)` is even.
5. **Case on `v(e)`.**
   - `v(e)` even: the point `(A, r₁)` lies on the curve for `ℓ = e`, so `v(A) = k` is even.
     Contradiction.
   - `v(e)` odd: `v(eH) = v(e) + 3k` is even. The point `(Az², z r₂)` lies on the curve for
     `ℓ = eH`, because `(z r₂)² = z² T₂`, by `ring`. So `v(Az²) = k + 2v(z)` is even.
     Contradiction.

Compared with upstream, the hypothesis `p ≠ 3` and the lemma `v_p(3l) = v_p(l)` are no longer needed.

## Kernel computations whose value changed

None. No `decide`/`rfl` table involves the pole coefficients.
- `poleBuild_run` is still `rfl`; it is a symbolic `Poly` equality.
- The params and witness counts of the template are unchanged: 1 and 11.

## Lemmas added beyond the leaves

All three were grep-checked for name clashes under `ZInQKernel/`:
- `ZInQ.Mult.poleSystem`
- `ZInQ.Mult.congruentCurve_rhs_nonzero_and_valuation`
- `ZInQ.Mult.poleSystem_no_negative_odd_valuation`

## Build times

- Changed modules alone (`Parity`, `PoleObstruction`, `Templates.Core`): 17 s.
- Full `lake build ZInQKernel`: 4 min 31 s wall time (15 min user). It rebuilt 177 modules
  downstream of `Syntax/Templates/Core.lean`.
  - Pole-related modules: `Size.Majorants.Templates` 10 s, `Assembly.Values.ValueTest` 24 s,
    `Syntax.Builder.Scope` 4 s.
  - Slowest rebuilt module: `Syntax.Recipes.PowerValue`, 54 s.
- `#print axioms` check: 5 s.

## Problems / not done

- I did not touch `construction/` (cross-checks only). These still encode the manuscript's
  `x + 3ℓ` polynomial, so the pole blocks of the saved `P_*` JSON no longer match the Lean `polePoly`:
  - `construction/multiplication-certificate.js` (the `pole` definition: `b.scale(3, e)` and
    `b.scale(3, b.mul(e, H))`);
  - `construction/variable-shift-polynomial-library.js`;
  - the saved `P_*` JSON.
- Upstream `lean/ZInQ/PolePolynomial.lean` (frozen) also still encodes the `x + 3ℓ`
  polynomial. Nothing in `ZInQKernel` uses it.

## Suggestions for the next agent

- Regenerate the construction cross-checks with the factor 3 removed in the `pole` definition.
- Update the blueprint articles for `Q_pole`, abscissa parity and PC to Route K.
- `KERNEL_PLAN.md` should record that PC now concerns the Route K polynomial: Kriz's 2-converse
  for congruent number curves replaces RC.
