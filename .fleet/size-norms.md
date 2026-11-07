# size-norms: report

All nine leaves of `blueprint/roadmap/size/norms/` are formalized and proved, with no `sorry`.
`#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` for every leaf
theorem. Modules: `ZInQKernel/Size/Norms/*.lean`, root `ZInQKernel/Size/Norms.lean`
(imported from `ZInQKernel.lean`). Namespace `ZInQ.Size`.

| Article | Lean name | Status |
| --- | --- | --- |
| size/norms/l1-norm.md | `ZInQ.Syntax.l1` (already on main), `ZInQ.Size.PairRing`, `ZInQ.Size.pairNorm`, `ZInQ.Size.pairDeg` (Defs.lean) | proved (definitions) |
| size/norms/l1-norm-estimates.md | `ZInQ.Size.l1_estimates` (bundles all items); new pieces `l1_eq_zero_iff`, `l1_smul`, `l1_C_mul`, `l1_natCast`, `l1_ofNat`, `l1_intCast` (Estimates.lean) | proved |
| size/norms/substitution-bounds.md | `ZInQ.Size.substitution_bounds`, `ZInQ.Size.rename_bounds`, `ZInQ.Size.l1_rename_eq`; pieces `totalDegree_bind₁_le`, `l1_rename_le` (Substitution.lean) | proved |
| size/norms/pair-norm.md | `ZInQ.Size.pair_norm_estimates` (bundles all items); pieces `pairNorm_add_le`, `pairNorm_sub_le`, `pairNorm_smul`, `pairNorm_mul_le`, `pairNorm_pow_le`, `pairDeg_add_le`, `pairDeg_mul_le`, `l1_re_le_pairNorm`, `l1_im_le_pairNorm`, `pairNorm_const`, `pairDeg_const`, `pairNorm_var`, `pairDeg_var` (Pair.lean) | proved |
| size/norms/quadratic-heights.md | `ZInQ.Size.QRep` (`val`, `size`), `QRep.exists_add`, `exists_sub`, `exists_mul`, `exists_two_mul`, `exists_div`, `QRep.coord_bounds` (Quadratic.lean) | proved |
| size/norms/division-polynomial-size.md | `ZInQ.Size.normDiv_size` (= `divF_size`), `ZInQ.Size.psiComponent_size` (DivisionPolynomials.lean) | proved |
| size/norms/coordinate-heights.md | `ZInQ.Size.iota_coord_height` (Coordinates.lean) | proved |
| size/norms/guard-size.md | `ZInQ.Size.guardPoly_size` (Guard.lean) | proved |
| size/norms/constructor-bounds.md | `ZInQ.Size.psi_uniform`, `ZInQ.Size.guard_uniform`, `ZInQ.Size.const_uniform` (Constructors.lean) | proved |

## Statement notes and corrections

No article statement was wrong. Differences in form:

- **l1-norm.** The ℓ¹ norm was already on main as `ZInQ.Syntax.l1`
  (`ZInQKernel/Syntax/Language/Size.lean`), with most of the elementary estimates and
  `l1_bind₁_le`. I reused it rather than define a second `ZInQ.Size.l1` as the
  implementation note suggests. The `lean:` field should name `ZInQ.Syntax.l1`. Pairs are
  `PairRing σ := QuadraticAlgebra (MvPolynomial σ ℤ) 2 0`, and `ZInQ.Syntax.ComponentRing`
  is `PairRing (Fin 4)`.
- **substitution-bounds.** The degree bound `totalDegree_bind₁_le` needs no hypothesis
  `d ≥ 1`. The bundled `substitution_bounds` keeps the article's hypotheses. The renaming
  equality `‖P(Y_σ)‖₁ = ∑_β |∑_{α↦β} c_α|` is `l1_rename_eq`.
- **pair-norm (5).** The hypothesis `i ≠ j` is not needed and goes unused.
- **quadratic-heights.** `QRep` is a structure `(a, b, c, c ≠ 0)` with
  `val = ⟨a/c, b/c⟩ : K0` and `size = max |a| (max |b| |c|)`. The sharper intermediate
  bounds are also proved: `size_add_le`/`size_sub_le` give `2H²`, `size_mul_le` gives `3H²`,
  `size_two_mul_le` gives `2H`, and `size_div_le` gives `3H³`.
- **division-polynomial-size.** `F_n := (normDiv componentA n).eval compX` (`divF n`),
  with `compX = ⟨X 0, X 1⟩` and `compY = ⟨X 2, X 3⟩`. Sizes are tracked through
  `Sz u d e := pairDeg u ≤ d ∧ pairNorm u ≤ 2^e`. The proof uses cruder base constants than
  the sketch: `‖D₀‖ ≤ 2^40` instead of `2^38`, and `F₃`, `F₄` bounded through powers of
  two. The slack of `100·(9 or 10)` bits absorbs this. The induction never evaluates `normDiv`
  at a concrete index; the base cases `n ≤ 4` are symbolic.
- **coordinate-heights.** `T : ℕ` stands for "integer `T ≥ 0`". The proof follows the
  sketch, with these differences:
  - Each `ψ_m(P₀)` triple has size at most `2^{135(|m|+1)³} ≤ 2^{1080(T+1)³}`. The sketch's
    `H₀ = 2^{1280(T+1)³}` is weaker but also fine.
  - Four field-operation levels are used, each sending a size bound `2^h` to
    `3·2^{4h} ≤ 2^{8h}` (`Rep.add`, `sub`, `mul`, `two_mul`, `div`).
  - The final exponent is `4096·1080 (T+1)³ ≤ 2^30 (T+1)³`.

  It uses `ZInQ.iota_eq_psi` with `ZInQ.genP0_not_isOfFinAddOrder`.
- **guard-size.** `T : ℕ`, with `guardPoly (T : ℤ)`. The proof bounds `|(D/B_j)A_j|` by
  `D·2^K ≤ 2^{16K}` instead of `2^{15K}`, so each factor has norm `≤ 2^{32K+6}`. The final
  exponent `8(T+1)³(32K+6) ≤ 2^39 (T+1)⁶` still holds.
- **constructor-bounds.** `guard_uniform` takes `T : ℤ` with `0 ≤ T` and `T + 1 ≤ B`.
  `const_uniform` states the degree `0`, the norm `|c|`, and `|c| ≤ 2^{B⁸}`. It is stated
  for `C c` in any variable type; this is the value of a `fixed` node
  (`Node.denote … (.fixed e) = C (I.val e)`).

## Lemmas added beyond the leaves

- `Sz` and its calculus (`Sz.mono`, `mul`, `pow`, `add`, `sub`, `intCast_mul`, `ofNat`):
  degree and norm bounds as exponents of 2 for pairs.
- `Rep u h` (`u ∈ K₀` has a triple of size `≤ 2^h`) and its calculus, plus `Rep.coords`.
- `exists_int_eval`: for `deg P ≤ δ`, `|w_i| ≤ V` and `q ≤ V`, the number `q^δ P(w/q)` is an
  integer with absolute value `≤ ‖P‖₁ V^δ`.
- `rep_psiP0`: a triple for `ψ_k(P₀)` of size `≤ 2^{135(|k|+1)³}`. Also `p0Num`,
  `genX0_eq_p0Num`, `genY0_eq_p0Num`, `psiP0_coord`, `rep_genX0`, and `rep_fixed`, which
  bounds `x([n]P₀)` and `y([n]P₀)`.
- `tripleCode_height`, `card_falseTriples_le`, `totalDegree_guardFactor_le`,
  `l1_guardFactor_le`.
- Pair helpers: `pairNorm_neg`, `pairNorm_intCast_mul`, `pairNorm_one`, `pairNorm_natCast`,
  `pairNorm_ofNat`, `pairDeg_neg`, `pairDeg_sub_le`, `pairDeg_pow_le`, `pairDeg_smul_le`,
  `pairDeg_intCast_mul_le`, `pairDeg_one`, `pairDeg_natCast`, `pairDeg_ofNat`,
  `totalDegree_re_le_pairDeg`, `totalDegree_im_le_pairDeg`.

## Problems

None blocking. Finite computations are only small closed literal comparisons, closed by
`norm_num`/`decide`. No `*Check` hypotheses were needed.

One technical note: numerals inside `componentA` elaborate with a `NatCast` instance path
through `AddMonoidAlgebra.ring`, so `simp` with `l1_ofNat` does not fire on them. A `show`
followed by `rw` works (see `pairNorm_componentA`).

## Suggestions for the next agent

- The majorant chapter (`Maj B h P`) can use `substitution_bounds` / `ZInQ.Syntax.l1_bind₁_le`
  for `psi` and `guard` nodes, which are `bind₁` of the constructor polynomial. Combine
  with `psi_uniform` and `guard_uniform`.
- Each Lean `Constructors` record must instantiate `psi := ZInQ.Syntax.psiComponent` and
  `guard := ZInQ.Syntax.guardPoly` for these bounds to apply as stated.
