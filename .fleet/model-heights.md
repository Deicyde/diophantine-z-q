# model-heights: heights on C(K0) and the finite search for small points

Branch `wip/model-heights`. Modules under `ZInQKernel/Model/Heights/`. The root module is
`ZInQKernel/Model/Heights.lean`, and `ZInQKernel.lean` imports it. `lake build ZInQKernel` succeeds.
There is no `sorry`, `axiom` or `native_decide`. `#print axioms` on the main theorems shows only
`propext`, `Classical.choice` and `Quot.sound`. I merged `origin/wip/model-field` (including its
report) at the end.

## Status

| Article (`blueprint/roadmap/model/heights/`) | Lean name(s) (namespace `ZInQ`) | Status |
| --- | --- | --- |
| `x-height.md` | `hK0` (`= logHeight₁ x / 2`), `hx` (`= naiveHeight / 2`), `hx_some`, `hx_zero`, `hK0_nonneg`, `hx_nonneg`, `hx_neg` | proved |
| `x-height-formula.md` | `hK0_div`, `hK0_div_of_isCoprime`, `exp_two_mul_hK0_div_of_isCoprime`, `hK0_ratCast`, `hK0_nonneg` | proved |
| `duplication-forms.md` | `F2`, `G2` (via `dupF`, `dupG`), `x_two_smul_C`, `two_smul_C_of_y_eq_zero` | proved |
| `duplication-archimedean.md` | `duplication_archimedean` (upstream `ModelDuplication.duplication_bounds`), `duplication_bounds_emb` | proved |
| `duplication-common-divisor.md` | `duplication_common_divisor`, `gcd_F2_G2_dvd` | proved |
| `duplication-height-bounds.md` | `hx_two_smul_bounds` | proved |
| `canonical-height.md` | `canonHeight` | proved (definition) |
| `canonical-height-bounds.md` | `canonHeight_tendsto`, `two_canonHeight_le`, `hx_le_two_canonHeight`, `canonHeight_two_smul`, `canonHeight_neg`, `canonHeight_add_twoTorsion`, `canonHeight_nonneg` | proved |
| `canonical-height-quadratic.md` | `canonHeight_parallelogram`, `canonHeight_zsmul` (also `canonHeight_nsmul`, `canonHeight_zero`) | proved |
| `height-of-2r.md` | `hx_two_R`, `height_two_R_integer_facts` | proved |
| `height-comparisons.md` | `height_comparisons`, `log_height_comparison_one`, `log_height_comparison_two` | proved |
| `small-height-bound.md` | `canonHeight_R_pos`, `hx_lt_log_nine_of_multiple` | proved |
| `search-box.md` | `search_box`, `mem_search_of_hK0_lt` | proved |
| `square-test.md` | `SqTest`, `isSquare_iff_sqTest` | proved |
| `small-height-search.md` | `smallHeight_search` (with `fC`, `searchQ`, `qRoot`, `searchX2`, `searchX1`, `smallSurvivors`); kernel run `Search.searchCheck_eq_true` | proved |
| `r-torsion-translates.md` | `x_pointR_add_cT0`, `x_pointR_add_cTdelta`, `x_pointR_add_cTnegdelta` | proved |

Files: `XHeight`, `Formula`, `DuplicationForms`, `CommonDivisor`, `DuplicationBounds`, `Canonical`,
`Comparisons`, `SmallPoints`, `Translates`, `SquareTest`, `SearchCheck`, `SearchKernel`,
`SearchSound`, `Search`, `SearchBox`.

## The finite search (kernel computation)

- **Checker** (`SearchCheck.lean`). Everything is a `Nat.rec` loop over a counter, with `Bool`
  tests built from the GMP-accelerated `Nat` primitives (`Nat.beq`, `Nat.ble`, `%`, `/`, `Nat.gcd`,
  `Nat.log2`). Integer square roots use Newton's method; the result `r` is checked
  (`r² ≤ n < (r+1)²`), with a fallback to `Nat.sqrt`, so `fastSqrt = Nat.sqrt` is a theorem and
  correctness does not depend on Newton.
- **Enumeration.** From `b² - 4ac = 2k²` we get `b = 2b'`, `k = 2k'` and `ac = b'² - 2k'²`. The loop
  runs over `i = b' + 81 ∈ [0,162]`, `k' ∈ [1,81]`, and `a ∈ [max(⌈m/81⌉,1), 81]` with `a ∣ m`,
  `m ≤ 81a` and `gcd(a, 2|b'|, m/a) = 1`, where `m = |b'² - 2k'²|`. That is 538,695 inner steps.
  The result is `qList`, which has 7004 tuples.
- **Square test.** For `x = (U + V s)/a` we have `a⁴ f(x) = u + v s ∈ ℤ[s]`, with `(u, v) = alpha a U V`.
  The checker evaluates `possSq u v`, a *necessary* condition for being a square: `N = u² - 2v²`
  is a perfect square `t²`, and `2(u ± t)` is a perfect square for one sign (with `2u` a square
  when that root is `0`). Its soundness is `possSq_of_isSquare`. Exactly six irrational roots pass;
  they are listed in `survivorTuples` and are identified with
  `23-17s, (5-4s)/2, 3-s, 2+4s, 1+s, -3+s`. Among the rationals only `0` passes. The converse
  direction (survivors are squares) uses the explicit points: `R`, the three translates, and the
  two-torsion.
- **Soundness of the enumeration.** It is proved from the code, not by evaluation:
  `mem_qList_iff`, `qList_nodup` and `mem_searchQ_iff`. `|𝒬| = qList.length = 7004`.
- **Kernel time.** `searchCheck_eq_true : searchCheck = true := by decide +kernel` sits in one module
  (`SearchKernel.lean`) and takes about 60 s on this host (61 s wall clock including the Mathlib
  import, measured at load about 15). No chunking was needed. The 111 rationals are part of the
  same check. The count `|𝒳₁| = 111` is a separate `decide +kernel` on a 171-element filter and is
  instant.
- **Kernel speed.** Loops that go through `Decidable` instances on `Int` (`|x|`, `Int.gcd`, `∧` of
  propositions) ran at about 800 steps/s. The `Nat.rec` + `Bool` + `Nat` primitive style ran at
  about 15,000 steps/s.

## Differences between the articles and the Lean statements

1. **x-height-formula.** "`g` a greatest common divisor" is stated as three hypotheses:
   `g ∣ a`, `g ∣ b`, and `∀ d, d ∣ a → d ∣ b → d ∣ g`. Mathlib has no `IsGCD` predicate, and `ℤ[s]`
   has no normalized gcd. `N(g)` is the integer `QuadraticAlgebra.norm g`.
2. **duplication-forms.** "`[2]T ≠ O` and `x([2]T) = F₂/G₂`" is stated as
   `∃ y' h', 2 • T = some (F₂/G₂) y' h'`. Here `a, b ∈ ℤ[s]` are mapped into `K₀` by `Zs.toK0`.
3. **duplication-common-divisor.** "Not both zero" is the hypothesis `F₂ ≠ 0 ∨ G₂ ≠ 0`. The proof
   shows `g ∣ s⁶δ⁴`, so the maximality of `g` is not needed: any common divisor satisfies the bounds.
   The valuation statements use the model-field valuation `vp`. The norm bound reads
   `(N g).natAbs ≤ 392²`.
4. **canonical-height-bounds (3)** and **small-height-bound (2)**: `T ∈ C(K₀)[2]` is the hypothesis
   `2 • T = 0`, and `m : ℤ` with `3 ≤ |m|`.
5. **search-box.**
   - Part (1) is proved with the stronger bound `|p| ≤ 8`, `1 ≤ q ≤ 8`.
   - Part (2) gives `1 ≤ a ≤ 81`, `|b| ≤ 162`, `|c| ≤ 81`, `gcd = 1`, `b² - 4ac = 2k²`,
     `1 ≤ k ≤ 162`, `x = (-b ± ks)/(2a)` and `a x² + b x + c = 0`, all as in the article. The proof
     actually gives `a ≤ 80`, `|b| ≤ 161`, `|c| ≤ 80` and `k ≤ 161`.
   - "Minimal polynomial" is not stated separately; it follows from primitivity and `x ∉ ℚ`.
   - The proof uses `x = α/β` with `N(β) > 0` (multiply by `ε` if needed) and the integer polynomial
     `N(β)X² - Tr(αβ̄)X + N(α)` divided by its content. Vieta's relations are taken from the
     components in `K₀`, not from the real roots.
6. **square-test.** `η` is a rational in `{1, -1}`. The article's remark that `Sq` is decidable by
   integer square roots is not formalized. The search does not use `Sq`; it uses the integral
   necessary test `possSq` described above, which leads to the same conclusion.
7. **small-height-search.**
   - `𝒳₂` is the image of `𝒬 × {1,-1}` under `qRoot`, with `k = Int.sqrt((b²-4ac)/2)`.
   - "The roots counted with their sign number 14008" is strengthened to `searchX2.card = 14008`:
     the roots are distinct elements of `K₀`. This uses a content argument (`qRoot_inj`).
   - `𝒳₁` is a `Finset ℚ`, and the equivalence is stated for `x ∈ 𝒳₁.image (↑) ∪ 𝒳₂`.

## Lemmas added beyond the leaves

- Infinite places of `K₀`: `wPlus`, `wMinus`, `infinitePlace_K0` (exactly two places, both of
  multiplicity 1) and `prod_infinitePlace_K0`.
- Finite places: `finprod_finitePlace_eq_one` (product 1 for coprime `a, b`), with `toOK : ℤ[s] → 𝓞 K₀`.
- Fractions: `exists_coprime_fraction`, `exists_coprime_fraction_pos`.
- Specific heights: `hK0_delta` (`h(δ) = ½ log 7`), `hx_approx_parallelogram`.
- Group law on `C`: `tangent_x_formula`, `curveC_two_smul_some`, `curveC_add_of_X_ne` (chord rule).
- Divisors of the duplication forms: `prime_dvd_F2_G2`, `not_sqrt2Z_pow_seven_dvd_F2`,
  `not_deltaZ_pow_five_dvd_F2`, `associated_of_prime_factors`.
- `small_point_abscissa`: an affine point `S = (x, y)` with `h_x(S) < log 9` has `x` in the seven
  survivors. It combines `search_box` and `smallHeight_search`.

## Problems met

- The elaborator evaluated the finite set `searchQ` while checking any hypothesis
  `(a, b, c) ∈ searchQ` passed as an argument, and hit the maximum recursion depth. Fixed with
  `attribute [irreducible] searchQ`; `simp only [searchQ, ...]` still unfolds it. The kernel is not
  affected.
- `linarith` failed on goals containing `Real.log (41 ^ 3 * 676)` because the atoms did not match.
  Fixed by generalizing the log terms first.
- `(QuadraticAlgebra.norm β : ℝ)` elaborates the norm over `ℝ`. Write
  `((QuadraticAlgebra.norm β : ℤ) : ℝ)`.

## Suggestions for the next agent

- The generator argument (`model/generator.md`) can chain three results: `hx_lt_log_nine_of_multiple`
  gives `h_x(S) < log 9`; `small_point_abscissa` then gives `x(S) ∈ {0, ±δ, 1+s, 23-17s, 2+4s,
  (5-4s)/2}`; and `x_pointR_add_*` / `canonHeight_R_pos` handle the translates of `R`.
- `hx` is half of Mathlib's `naiveHeight` (`naiveHeight_eq_two_mul_hx`), so the rest of Mathlib's
  height API (Northcott, finiteness of torsion) applies directly to `curveC`.
- If the kernel run is ever too slow on a loaded machine, split `iLoop` by ranges of `i` into
  separate modules and add the lengths.
