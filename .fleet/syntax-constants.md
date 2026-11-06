# syntax-constants: report

Blueprint chapter `syntax/`, section `constants/`. Lean modules are in `ZInQKernel/Syntax/Constants/`,
the root module is `ZInQKernel/Syntax/Constants.lean`, and everything is in namespace `ZInQ.Syntax`.
There are no `sorry`s, `native_decide`s or axioms. `#print axioms` on the main results reports only
`propext`, `Classical.choice` and `Quot.sound`. `lake build ZInQKernel` passes.

## Leaves

| Article | Lean name(s) | Status |
| --- | --- | --- |
| `syntax/constants/prime-catalogue.md` | `unitResidues`, `cataloguePrime`, `catalogueProduct`, `catalogueMax` (`Catalogue.lean`) | proved |
| `syntax/constants/least-formal-multiple.md` | `IsNormalizedRep`, `normalizedRep`, `xi`, `FormalCondition`, `leastFormalMultiple` (`FormalMultiple.lean`) | proved |
| `syntax/constants/fixed-integer-expressions.md` | `FixedExpr`, `FixedExpr.val` (`Expr.lean`) | proved |
| `syntax/constants/fixed-constants.md` | `FixedConst`, `FixedConst.expr`, `FixedConst.value`, `fixedVal`; `Ps W Hcat Hmax Ns M0 cstar ell F D G0 E0 R Q Bcm Ccm Aht T`; `FixedConst.value_P0` … `value_T` (`Fixed.lean`), facts in `Relations.lean` | proved (except `integer_constant_0..4`, see below) |
| `syntax/constants/primorial-literal.md` | `primorial_324_eq`, `four_mul_primorial_324_eq`, `card_primes_le_324`, `digits_two_primorial_324_length`, `digits_two_four_mul_primorial_324_length` (`PrimorialLiteral.lean`) | proved (kernel `decide +kernel`) |
| `syntax/constants/guard-product.md` | `guardBox`, `falseTriples`, `tripleCode`, `tripleDen`, `guardFactor`, `guardPoly` (`Guard.lean`) | proved |

## What is proved

- **Catalogue.** For `r ∈ unitResidues W`, Dirichlet's theorem (Mathlib) gives `cataloguePrime_spec`
  (the prime is genuine, `> B`, and `≡ r`). Also proved: strict monotonicity, the "first k" property
  `exists_cataloguePrime_eq_of_lt`, injectivity in `(r, j)`, `catalogueProduct_pos`, divisibility,
  `≤ max`, `catalogueMax_le_catalogueProduct`, `catalogueMax_eq_zero_or_exists`, coprimality with
  `B#`, and `catalogueProduct = ∏ catalogueFinset`.
  Bridges to `Hypotheses/PrimePattern.lean`: `ZInQ.cataloguePrime r i = cataloguePrime catalogueModulus 324 r i`
  holds by `rfl`, `catalogueSet_eq`, and `catalogueMax_lt_of_catalogueBound` (CAT ⇒ `H_max < 2^(W³)`).
- **Least formal multiple.** `normalizedRep u = (u₀ c, u₁ c, c)` with `c = lcm(den u₀, den u₁)`.
  Existence and uniqueness of the normalized representation: `normalizedRep_isNormalizedRep` and
  `IsNormalizedRep.eq_normalizedRep`. `normalizedRep 0 = (0,0,1)`.
  `leastFormalMultiple N = sInf {m | 1 ≤ m ∧ FormalCondition N m}`, which is `0` when no index works.
  Proved: `leastFormalMultiple_spec` (if some index succeeds then LFM is the least one),
  `leastFormalMultiple_eq_zero`, `leastFormalMultiple_eq_of`, `leastFormalMultiple_pos_iff`.
- **Fixed expressions.** `val` is defined by structural mutual recursion with `valMax`. The defining
  equations `val_literal` … `val_max` hold, plus `val_max_le_iff` and `le_val_max`. `val_congr` says the
  value depends only on the referenced names (`refs`). There are ℕ-transfer lemmas `val_*_eq`.
- **Constants.** `FixedConst.expr` copies `library.fixedConstants` of the saved specification node for
  node. `FixedConst.expr_refs_lt` (every expression refers only to earlier names) is checked by `decide`.
  `value` is well-founded recursion over specification order, and `value_eq_val` gives
  `value c = (expr c).val value`. Each `value_X : X.value = (X : ℤ)` identifies the syntactic value with
  the ℕ constant defined by the table's formula. The defining equations are `Ps_eq`, `W_eq`, …, `T_eq`.
- **Relations** (`Relations.lean`):
  - The decimal literals `Ps_eq_literal` and `W_eq_literal`.
  - Bridges: `W_eq_catalogueModulus`, `Hcat_eq_catalogueModulus`, `Hmax_eq_catalogueModulus`,
    `Hcat_eq_prod_catalogueSet`.
  - Positivity of every constant except `M0` and `cstar`; `cstar_pos_iff` says `0 < cstar ↔ 0 < M0`.
  - Catalogue facts: `324 < Hmax`, `Hmax ≤ Hcat`, `Hmax_lt_of_catalogueBound`, `coprime_Ps_Hcat`,
    `Ps ∣ Ns`, `Hcat ∣ Ns`, `Ps ∣ W`, and divisibility and bounds for each catalogue prime.
  - `M0_spec`, `M0_eq_zero`.
  - `F ∣ D`; `D`, `Hmax`, `cstar`, `10¹²` are each `≤ R`; `R ≤ Q`.
  - `2·10¹³ ≤ Aht`, `2·10¹³·Ccm ≤ Aht`, `2·10¹³·Q¹⁷ ≤ Aht`, `Aht ≤ T`.
  - Bridges to upstream: `F_eq_factorialBase`, `D_eq_explicitCutoffBounds_d`, `G0_eq_g0`.
- **Guard.** `guardPoly T = ∏_{t ∈ falseTriples T} guardFactor t` holds by definition. Also proved:
  `den_dvd_tripleDen` (`B_j ∣ D_abc`), `tripleDen_pos`, `tripleCode_apply` and `tripleCode_eq_iff`
  (point-major layout), `eval_guardFactor`, `eval_guardFactor_eq_zero_iff`, and
  `guardPoly_eval_eq_zero_iff`: the rational zero set of `G_T` is exactly the set of codes of false triples
  `(a,b,c)`, `|a|,|b|,|c| ≤ T`, `ab ≠ c`. `guardPoly_of_neg` gives `1` for `T < 0`.

## Statement corrections and choices

1. **fixed-constants: P0 and W.** A `FixedExpr` cannot express `∏_{p≤324} p`. So `FixedConst.expr` stores
   `P0` and `W` as the decimal literals of the saved specification, exactly as the JSON does. The ℕ
   constants are defined by the table's formulas: `Ps := primorial 324` and `W := 4·Ps`. `value_P0` and
   `value_W` identify the two through the decimal check (`primorial_324_eq`).
2. **fixed-constants: `integer_constant_0..4`.** These are not defined here. The article says they are bound
   by the model-evaluation translation, and `c_3` has 3,181,317 digits. That belongs to the compiler or
   translation task.
3. **prime-catalogue: indexing.** `cataloguePrime W B r j` is `p_{r,j+1}` (counting from 0), and the class
   condition is `p % W = r` for `r < W`, which is equivalent to `p ≡ r (mod W)`. This matches
   `ZInQ.cataloguePrime` definitionally. The residue set is literally the article's `1 ≤ r < W`,
   `gcd(r,W) = 1`. For `W = 1` it is empty, so the product is `1` and the max is `0`. This does not matter
   for the fixed catalogue.
4. **least-formal-multiple.** The multiple is `m • P₀` with `m : ℕ`. `ξ(Q) = x(Q)⁻¹` for affine `Q`; Lean's
   `0⁻¹ = 0` gives the article's convention at `x = 0`. The gcd condition is
   `Nat.gcd (Int.gcd a b) c = 1`. The definition is total in `N`, including `N = 0`.
5. **guard-product.** `guardPoly : ℤ → MvPolynomial (Fin 15) ℤ` matches the `guard` field of
   `Syntax.Constructors`. The box is `Finset.Icc (-T) T`³ and is empty for `T < 0`. `tripleCode` uses
   `ι` (`ZInQ.iota`) directly, as the article says.
6. **Naming.** Everything is in `ZInQ.Syntax`, following the implementation notes. The short global names
   (`W`, `D`, `F`, `R`, `Q`, `T`, …) shadow nothing, but files that open `ZInQ.Syntax` with autoImplicit
   should take care.

## Lemmas beyond the leaves

These are the catalogue lemmas, the normalized-representation lemmas, the transfer lemmas, the
relations, the zero-set lemmas listed above, and the following helpers:
- `isPrimeB`, `isPrimeB_iff` and `primorialB`, `primorialB_eq`: a sound structural kernel checker.
- `FixedFormula.*`: the formulas as functions of the earlier constants, with generic equations.
- `fixed_val`: a tactic macro.
- `fixedVal`: the specification's value map.

## Problems encountered (important for other agents)

- **The kernel evaluates closed `Nat` arithmetic whenever it compares non-syntactic terms.**
  - **Cause.** The kernel unfolds instance projections (`HMul.hMul`, abbrev hints) first, reaches for
    example `Nat.mul Ps Hcat`, and then its GMP extension whnf's both arguments to try to get literals.
  - **Example.** The auto-generated equation lemma of `def Ns := Ps * Hcat` (from `rw [Ns]` or `unfold`)
    makes the kernel try to evaluate `catalogueProduct` over `range W`, and it hangs.
  - **Example.** `exact Nat.succ_pos _` against `0 < D^2 * 3^… + 1` produces
    "kernel refused to evaluate Nat.pow".
  - **Example.** A core lemma stated with `instPowNat`, such as `Nat.two_pow_pos`, used against
    Mathlib's `Monoid.npow` form `2 ^ W ^ 3` fails the same way.
  - **Remedy used here.**
    - Each constant's body is a formula function applied to earlier constants (`Ns := FixedFormula.Ns Ps Hcat`).
    - Equations are instances of generic lemmas over variables.
    - The constants and `FixedExpr.val` are marked `irreducible` after their equations, so the elaborator
      cannot unfold them.
    - Downstream code must reason only through `Ps_eq`, …, `T_eq`, `value_*`, and Mathlib lemmas such as
      `pow_pos`. Never use `rfl`, `decide`, `simp` arith or core `Nat` lemmas whose statement is not
      syntactically the goal.
    - The let-variable trick also works (see `D_eq_explicitCutoffBounds_d` or upstream `d_def`): fvars
      disable the kernel's `Nat` evaluation.
- **`simp` on goals containing `FixedConst.value` produced proofs that made the kernel unfold the
  well-founded `value`.** Use the `value_*` lemmas and the `fixed_val` macro instead.
- **Failed unification inside `first | exact … | refine …` made Meta whnf `val value (catalogueProduct …)`,
  that is, a `Finset.prod` over `range W`.** This is fixed by the `irreducible` attributes.
- **Lean output through a pipe is block-buffered.** Use `stdbuf -oL` to see which declaration hangs.

## Suggestions for the next agent

- The size chapter should use `Relations.lean` together with `F_eq_factorialBase` and
  `D_eq_explicitCutoffBounds_d` to reuse upstream bounds on `F` and `D`. The existence of a successful
  index for `N_s` (so `M0 ≥ 1` via `M0_spec`) is still open.
- The guard-template semantics (`syntax/templates/guard-semantics.md`) can use
  `guardPoly_eval_eq_zero_iff` together with `MvPolynomial.eval₂_bind₁` for the node substitution.
- A `Syntax.Constructors (FixedExpr FixedConst)` instance can be assembled as
  `⟨fixedVal, <division-polynomial components>, guardPoly⟩` once the `psi` components exist.
