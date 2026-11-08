# pp-idealcount: plan step 3.3, ideal counts in quadratic fields

All four items are proved, with no `sorry`. Every delivered theorem depends only on
`propext`, `Classical.choice` and `Quot.sound` (checked with `#print axioms`). The modules
import only Mathlib and each other: `ZInQKernel/Progressions/IdealCount/{Basic, PrimePower,
Splitting, ZetaFactor}.lean`, with root `ZInQKernel/Progressions/IdealCount.lean`. Everything
is in namespace `ZInQ.Progressions`; helpers are in `ZInQ.Progressions.IdealCount`. No
finite-computation hypotheses were needed.

`a_K(n)` is `ZInQ.Progressions.idealCount K n := Nat.card {I : Ideal (𝓞 K) // absNorm I = n}`.
`dedekindZeta_eq_LSeries_idealCount` (proved by `rfl`) states that these are the coefficients
of `NumberField.dedekindZeta`. `ε_p` is the explicit
`localEps K p : ℤ := idealCount K p - 1`.

| article path (bp-progressions branch) | Lean name | status |
| --- | --- | --- |
| progressions/ideal-counts/ideal-count.md | `idealCount`, `dedekindZeta_eq_LSeries_idealCount`, `IdealCount.LSeriesSummable_idealCount` (summable for `1 < re s`, any number field) | proved |
| progressions/ideal-counts/multiplicative.md | `idealCount_mul` (coprime `m n`, any number field), `idealCount_one` | proved |
| progressions/ideal-counts/local-factors.md | `localEps`, `localEps_mem`, `idealCount_prime_pow`, `exists_localFactor` (the existential form of item 2), `eq_localEps_of_idealCount_prime_pow` (the `ε` is unique), `idealCount_prime_pow_cases`, `IdealCount.tsum_term_idealCount_prime_pow` (the Euler-factor form, complex `s` with `0 < re s`) | proved |
| progressions/ideal-counts/splitting-law.md | `localEps_eq_legendreSym`, `idealCount_prime_eq_legendreSym`, `idealCount_prime_pow_eq_legendreSym` | proved |
| progressions/ideal-counts/zeta-factorization.md | `dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod` (the form step 3.4 needs), `dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod_of_legendreSym` (combined with the splitting law), `dedekindZeta_eq_mul_prod_of_localEps_eq` (any finite set `P` of primes, complex `s` with `1 < re s`) | proved |

## Delivered statements (hypotheses abbreviated)

- Item 1. `idealCount_mul (h : m.Coprime n) : idealCount K (m * n) = idealCount K m * idealCount K n`.
- Item 2. With `h2 : Module.finrank ℚ K = 2` and `hp : p.Prime`:
  `localEps K p = -1 ∨ localEps K p = 0 ∨ localEps K p = 1`, and
  `∀ k, (idealCount K (p ^ k) : ℤ) = ∑ j ∈ Finset.range (k + 1), localEps K p ^ j`.
- Item 3. Assume `h2`, `α : 𝓞 K`, `hα : α ^ 2 = d` with `d : ℤ`, `hd : ¬ IsSquare d`,
  `[Fact p.Prime]`, `p ≠ 2` and `¬ (p : ℤ) ∣ d`. Then `localEps K p = legendreSym p d`.
- Item 4. Assume `h2`, `q ≠ 0`, `χ : DirichletCharacter ℂ q`, and
  `hχ : ∀ p, p.Prime → ¬ p ∣ 2 * q → (localEps K p : ℂ) = χ p`. Then for real `s > 1`:
  `dedekindZeta K s = riemannZeta s * LSeries (fun n ↦ χ n) s *
     ∏ p ∈ (2 * q).primeFactors, (1 - χ p * p ^ (-s)) * (1 - localEps K p * p ^ (-s))⁻¹`.
  The `_of_legendreSym` variant replaces `hχ` by two hypotheses:
  `∀ p, p.Prime → ¬ p ∣ 2 * q → ¬ (p : ℤ) ∣ d` and
  `∀ p [Fact p.Prime], ¬ p ∣ 2 * q → χ p = legendreSym p d`.
  It also takes `α`, `hα` and `hd` as in item 3.

## Statement corrections

1. **The splitting law (item 3) needs `d` to be a non-square.** As the task states it, the
   claim is false when `d` is a perfect square. Example: `K = ℚ(i)`, `α = 1`, `d = 1`, `p = 3`.
   Here `p` is inert, so `ε_3 = -1`, but `(1/3) = 1`. The Lean statement adds
   `hd : ¬ IsSquare d` (over `ℤ`). The blueprint article (`d` squarefree, `d ≠ 1`,
   `K = ℚ(√d)`) is correct, and it is a special case of the Lean statement. The Lean statement
   covers any quadratic field `K` and any `α ∈ 𝓞 K` with `α² = d`.
2. **Item 4 needs `q ≠ 0`.** For `q = 0` every prime divides `2q`, so `hχ` is vacuous, but
   `(2·0).primeFactors = ∅` and the identity fails.
3. `ε_p` and the identity of item 2 live in `ℤ`. The Legendre symbol needs a
   `[Fact p.Prime]` instance, so item 3 takes `p` that way.
4. Item 4 as the task describes it ("write a_K as the Dirichlet convolution of 1, ψ and local
   corrections") was not formalized in convolution form. The L-series identity, which is the
   deliverable, is proved directly by comparing Euler products. It is stated for Dirichlet
   characters, which is the form the later task needs, and not for a general completely
   multiplicative `ψ`. The general-`P` version `dedekindZeta_eq_mul_prod_of_localEps_eq`
   covers any finite set of primes.

## Proof route (differs from the plan in step 3)

- Items 1 and 2 use plain ring theory and unique factorization. They do not use Mathlib's
  ramification API, which is being deprecated in this Mathlib version.
  - Item 1. For norms `m`, `n` coprime: `I = IJ + (m)` and `L = (L + (m))(L + (n))`.
    Norms: `absNorm (L + (m))` divides both `m ^ [K:ℚ]` and `mn`, hence divides `m`.
  - Item 2. `IdealCount.primePowEquiv` is a bijection. On one side are the ideals of norm
    `p^k`. On the other are the exponent vectors `a` on the primes above `p` with
    `∑ a_P f_P = k`. It is built from `normalizedFactors` and its inverse `∏ P ^ a_P`.
    Applied to `(p)`, it gives `∑ e_P f_P = [K:ℚ]`. For a quadratic field this leaves three
    cases: residue degrees `{2}`, `{1}` or `{1, 1}`. They give `a(p^k) = [k even]`, `1`,
    `k + 1`.
- Item 3 uses no Kummer–Dedekind and no index computation.
  - Ideals of norm `p` correspond bijectively to ring homomorphisms `𝓞 K → ZMod p`, via
    kernels. This uses `ZMod.ringHom_eq_of_ker_eq` and `ZMod.ringEquivOfPrime`.
  - With `t = Algebra.trace ℤ (𝓞 K)`, every `x ∈ 𝓞 K` satisfies
    `2 d x = d t(x) + t(α x) α` (`IdealCount.two_mul_mul_eq`). This is proved in `K` with
    the basis `{1, α}` and `Tr α = 0`.
  - So a homomorphism is determined by `r = φ(α)`, which satisfies `r² = d`, because `2d`
    is invertible mod `p`. Conversely, `x ↦ (d t(x) + t(αx) r)/(2d)` is a homomorphism
    (`IdealCount.sqrtHom`). Multiplicativity comes from two trace identities, obtained by
    comparing coefficients in the basis `{1, α}`.
  - Hence `a_K(p) = #{r : r² = d} = 1 + (d/p)`, by `legendreSym.card_sqrts`.
- Item 4: Euler products.
  - `EulerProduct.eulerProduct_hasProd` for `term a_K s`. Summability comes from Mathlib's
    count of ideals of norm `≤ t`, as in Mathlib's proof of the class number formula.
  - The Euler factor at `p` is a Cauchy product of two geometric series.
  - `riemannZeta_eulerProduct_hasProd` and `DirichletCharacter.LSeries_eulerProduct_hasProd`
    give the Euler products of `ζ` and `L`.
  - The corrections form a finitely supported `HasProd`. The result follows from
    `HasProd.unique`.

## Lemmas added beyond the leaves

In `ZInQ.Progressions`: `idealCount_sup_span_eq`, `idealCount_sup_mul_sup_eq`,
`idealCount_eq_of_dvd_of_dvd`, `idealCount_span_sup_span_eq_top`, `idealCount_absNorm_sup_eq`,
`idealCountMulEquiv`.

In `ZInQ.Progressions.IdealCount`:
- prime powers: `primesOver`, `resDeg`, `span_natCast_ne_bot`, `mem_primesOver`,
  `absNorm_of_mem_primesOver`, `resDeg_pos`, `ne_bot_of_absNorm_eq`,
  `normalizedFactors_subset`, `absNorm_prod`, `prod_count_eq`, `count_prod_eq`,
  `primePowEquiv`, `idealCount_pow_eq_card`, `sum_count_mul_resDeg` (`∑ e f = [K:ℚ]`),
  `sum_resDeg_le`, `primesOver_nonempty`;
- counting: `card_single`, `card_pair`, `card_mul_one`, `card_mul_two`;
- prime norm and the trace identity: `absNorm_ker`, `idealCount_prime_eq_card_ringHom` (any
  number field), `linearIndependent_one_sqrt`, `trace_one_eq_two`, `trace_sqrt_eq_zero`,
  `trace_sqrt_sq`, `two_mul_mul_eq_field`, `coe_trace_int'`, `coe_sq_eq`, `two_mul_mul_eq`,
  `trace_one_int`, `trace_sqrt_int`, `trace_sq_int`, `eq_zero_of_add_mul_eq_zero`,
  `trace_mul_identities`;
- homomorphisms and square roots: `sqrtHom`, `sqrtHom_apply_sqrt`, `card_ringHom_eq_card_sqrt`;
- zeta function: `tendsto_sum_idealCount_div`, `LSeriesSummable_idealCount`,
  `term_idealCount_one`, `term_idealCount_mul`, `hasProd_dedekindZeta`, `tsum_geom_sum_mul`,
  `natCast_pow_cpow`, `norm_natCast_cpow_neg_lt_one`, `norm_localEps_le_one`,
  `tsum_term_idealCount_prime_pow`.

## Problems

None blocking. Two Mathlib v4.35 points to know:
- `Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow` is not re-exported through
  `Mathlib.NumberTheory.NumberField.DedekindZeta` (a private import in the module system),
  so it has to be imported explicitly.
- `if_pos` and `if_neg` are deprecated.

The full `lake build ZInQKernel` passes.

## Suggestions for the next agent (steps 3.4 and 3.5)

- To use item 3 or item 4 with pp-quadfield's `Qsqrt d = QuadraticAlgebra ℚ d 0`:
  - Take `α : 𝓞 (Qsqrt d)` to be the generator `ω`, which is integral since `ω² = d`, and
    use `hα : α ^ 2 = d`.
  - Get `hd : ¬ IsSquare d` over `ℤ` from pp-quadfield's `¬ IsSquare (d : ℚ)` by
    `Rat.isSquare_intCast_iff`.
  - Use `h2 := Qsqrt.finrank`.
- The odd prime factors of `d` divide `q`, so `p ∤ 2q` gives `¬ (p : ℤ) ∣ d`. This is the
  hypothesis `hdq` of `dedekindZeta_eq_riemannZeta_mul_LSeries_mul_prod_of_legendreSym`.
- For the residue (3.5), multiply the item 4 identity by `s - 1` and use
  `NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT` together with
  `riemannZeta_residue_one`. The finite product is continuous at `s = 1`. Its denominators
  are nonzero because `|ε_p| ≤ 1 < p`: see `IdealCount.norm_localEps_le_one` and
  `IdealCount.norm_natCast_cpow_neg_lt_one`, which hold for `0 < re s`.
