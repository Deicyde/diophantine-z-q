# assembly-close: the relation Close, its soundness and its completeness

Directory `ZInQKernel/Assembly/Close/`, root module `ZInQKernel/Assembly/Close.lean`
(imported from `ZInQKernel.lean`). `lake build ZInQKernel` succeeds.

| Article | Lean name | Status |
| --- | --- | --- |
| assembly/approximation/close-relation.md | `ZInQ.Assembly.close_relation_iff` | proved |
| assembly/approximation/close-soundness.md | `ZInQ.Assembly.close_sound` | proved |
| assembly/approximation/close-completeness.md | `ZInQ.Assembly.close_complete` | proved |

The only hypothesis is the multiplication statement M:
`hM : Translation.MultiplicationExact Syntax.specConstructors FixedConst.cstar.value
FixedConst.ell.value FixedConst.T.value`. `HaltingNodeCheck` is not needed. The three
theorems use `Compiler.natural_polynomial_semantics'`, so `#print axioms` currently shows
`sorryAx`. That sorry is the wrapper-correctness `sorry` inside
`Compiler.natural_polynomial_semantics` (being removed by another task). Every other dependency
is sorry-free: `precision_rel_iff_accepts_of`, `spec_close_rel_iff`, `signedEncode_rel_iff`,
`closeCoordinates_rel_iff`, `natural_polynomial_semantics_of`, and the two real lemmas below
show only `propext`, `Classical.choice` and `Quot.sound`.

## Statements

`closeSpecLib` (an `abbrev`) is `specLib specConstructors FixedConst.cstar.value
FixedConst.ell.value FixedConst.T.value (Compiler.Universal.c3 : ℤ)
(precisionCircuitOf (Compiler.Universal.c3 : ℤ))`. This is the library of
`specPstar (Compiler.Universal.c3 : ℤ)` (`Syntax/Recipes/Literal.lean`). `Rel_close(N, K, t)` is
`ValRel (getEx closeSpecLib 2) (List.ofFn N ++ (List.ofFn K ++ [t]))`, the same form as
`spec_main_rel_iff` uses.

```lean
theorem close_relation_iff (hM : …) (N K : Fin 5 → ℚ) (t : ℚ) :
    ValRel (getEx closeSpecLib 2) (List.ofFn N ++ (List.ofFn K ++ [t])) ↔
      ∃ n κ a l : ℤ, N = iota n ∧ K = iota κ ∧
        accepts ![enc n, enc κ, enc a, enc l, enc (n * a)] ∧
        |t - rRatio a (n * a)| < epsIdx l

theorem close_sound (hM : …) (n κ : ℤ) (t : ℚ)
    (h : ValRel (getEx closeSpecLib 2) (List.ofFn (iota n) ++ (List.ofFn (iota κ) ++ [t]))) :
    (n : ℚ) ∉ contactSet ∧ κ ≠ 0 ∧ |(t : ℝ) - n| < Real.exp (-(bound n κ : ℝ))

theorem close_complete (hM : …) (n κ : ℤ) (hn : (n : ℚ) ∉ contactSet) (hκ : κ ≠ 0) :
    ValRel (getEx closeSpecLib 2) (List.ofFn (iota n) ++ (List.ofFn (iota κ) ++ [(n : ℚ)]))
```

`Prec(n, κ, a, l, j)` appears literally as `accepts ![enc n, enc κ, enc a, enc l, enc j]`.
`accepts_enc_iff` turns it into `acceptsInt n κ a l j`. `B(n, κ)` is
`Compiler.Precision.bound n κ = A0 * |κ * sixF n|^24`, and `bound_eq_heightH6` identifies it
with `H₆(S_ht) |κ F(n)|²⁴`. No large constant is ever evaluated.

## Statement corrections and naming

- The implementation note proposes the name `ZInQ.Assembly.close_rel_iff`, but that name
  already exists: it is the generic composition-recipe lemma in `Assembly/Values/Outer.lean`.
  The leaf is therefore `close_relation_iff`.
- The articles assume H, PC and 22P. In Lean these enter only through M, so the theorems take
  `hM`, as the task interface specifies.
- Contact set: the statements use `(n : ℚ) ∉ contactSet`, as in the implementation notes and
  `test_complete`. `cast_mem_contactSet_iff` converts to `n ∉ contacts`.
- No mathematical correction was needed.

## Lemmas added beyond the leaves (namespace `ZInQ.Assembly`)

- `Close/Relation.lean`: `closeSpecLib`; `accepts_enc_iff`; `ofFn_rows`, which shows that five
  rows of five rationals form the 25-entry list by `rfl`; and `spec_precision_iff`, the local
  `precision_rel_iff` of the implementation note. It chains `precision_rel_iff_accepts_of` with
  `natural_polynomial_semantics'` and states, for recipe 1 of the specification, that the
  relation holds iff `∃ c, (∀ i, E i = ι(c i)) ∧ accepts c`.
- `Close/Soundness.lean`: `exp_natCast_le_four_pow` (`e^B ≤ 4^B`) and
  `abs_sub_lt_exp_of_tests`. The second derives `|t - n| < e^{-B}` from the closeness,
  precision and window tests.
- `Close/Completeness.lean`:
  - `zPt_eq_zCoord`
  - `abs_re_add_abs_im_le` (`|u| + |v| ≤ |σ₊ w| + |σ₋ w|`)
  - `exists_abs_emb_z_lt` (`|σ(-x/y)| < θ` once `σ(x)` is large)
  - `exists_epsIdx_lt` (the choice of `l`)
  - `exists_rRatio_close` (the choice of `a`, from `z_ratio_tendsto` at both places and
    `exists_multiple_large`)

## Problems

None, apart from the upstream wrapper `sorry` described above.

## Suggestions for the next agent (assembly-top)

- Main-branch exactness: `close_sound` gives `(n : ℚ) ∉ contactSet`, `κ ≠ 0` and
  `|t - n| < exp(-(bound n κ))`. Combine it with `sixContact_at_heightPrimes` and
  `bound_eq_heightH6`, or with `A0` directly, since `bound n κ = A0 * |κ sixF n|^24`.
- Ordinary-value relation: `close_complete` takes any nonzero `κ`. Use it with the shift from
  `test_complete` inside `spec_main_rel_iff`. `getEx closeSpecLib 2` unfolds reducibly to
  `getEx (specLib … (precisionCircuitOf ↑c3)) 2`.
