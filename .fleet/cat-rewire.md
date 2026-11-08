# cat-rewire: plan step 5's interface (CatalogueBound → CatalogueBound8)

The size chain, the assembly lemma and the main theorems now take `ZInQ.CatalogueBound8`
instead of `ZInQ.CatalogueBound`. `lake build ZInQKernel` succeeds, `scripts/check_target.py`
reports that FrozenTarget is unchanged, and `#print axioms` on
`ZInQ.exists_bounded_integer_polynomial_defining_integers_of` (and on the `_catalogueBound`
corollary) gives only `[propext, Classical.choice, Quot.sound]`. No `sorry`, no new closed
decidable check hypotheses.

## New main theorem

```lean
theorem ZInQ.exists_bounded_integer_polynomial_defining_integers_of
    (hH : SixContactEstimate) (hPC : PoleCompleteness)
    (h22 : FixedPrimePattern) (hCAT : CatalogueBound8) : FrozenTarget
```

where

```lean
def ZInQ.CatalogueBound8 : Prop :=
  ∀ r : ℕ, r < catalogueModulus → Nat.Coprime r catalogueModulus →
    22 ≤ ({p ∈ Finset.Ioo 324 (2 ^ catalogueModulus ^ 8) |
      p.Prime ∧ p % catalogueModulus = r}).card
```

(`open Classical in`, exactly like `CatalogueBound` but with exponent `8` in place of `3`.)

## Table

| Plan step / file | Lean name | Status |
| --- | --- | --- |
| 5 / Hypotheses/PrimePattern.lean | `ZInQ.CatalogueBound8` | defined |
| 5 / Hypotheses/PrimePattern.lean | `ZInQ.catalogueBound8_of_catalogueBound : CatalogueBound → CatalogueBound8` | proved |
| 5 / Hypotheses/PrimePattern.lean | `ZInQ.cataloguePrime_lt_of_catalogueBound8` (`cataloguePrime r i < 2 ^ catalogueModulus ^ 8`) | proved |
| 5 / Main.lean | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of` (4th hyp. now `CatalogueBound8`) | proved |
| 5 / Main.lean | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_addMulBound`, `_of_nodeCheck` (same change) | proved |
| 5 / Main.lean | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_catalogueBound` (new corollary, takes `CatalogueBound`) | proved |
| 5 / Assembly/Top/Assembly.lean | `ZInQ.Assembly.Pstar_spec_of`, `Pstar_spec`, `assembly` (hyp. now `CatalogueBound8`) | proved |

## Restated theorems (same name, hypothesis `CatalogueBound8`, new numerals)

`ZInQ.Size` unless noted. Old → new.

- `Syntax/Constants/Catalogue.lean`: **renamed** `ZInQ.Syntax.catalogueMax_lt_of_catalogueBound`
  → `catalogueMax_lt_of_catalogueBound8`: `catalogueMax catalogueModulus 22 324 < 2 ^ catalogueModulus ^ 8`.
- `Syntax/Constants/Relations.lean`: **renamed** `ZInQ.Syntax.Hmax_lt_of_catalogueBound`
  → `Hmax_lt_of_catalogueBound8`: `Hmax < 2 ^ W ^ 8`.
- `Size/Constants/Catalogue.lean`:
  - `cataloguePrime_bounds`: `… < 2 ^ W ^ 3` → `… < 2 ^ W ^ 8`;
  - `Hcat_bounds`: `Hcat ≤ (2 ^ W ^ 3) ^ (22 * W)` → `Hcat ≤ (2 ^ W ^ 8) ^ (22 * W)`;
  - `catalogue_bounds`: all `W ^ 3` → `W ^ 8`;
  - `mul_lt_of_catalogue` (variables): hyp. `h ≤ (2 ^ w ^ 8) ^ (22 * w)`, concl. `p * h < 2 ^ 2 ^ 4613` (was `2054`);
  - `ell_lt_of_catalogue` (variables): same hyp., concl. `12 * (p ^ 2916 * h ^ 732) < 2 ^ 2 ^ 4623` (was `2063`);
  - `Ns_bounds`: `Ns < 2 ^ 2 ^ 4613` (was `2054`);
  - `ell_lt`: `ell < 2 ^ 2 ^ 4623` (was `2063`);
  - `catalogue_size`: both numerals updated;
  - helpers **renamed**: `pow_four_lt_of_lt` (`w⁴ < 2^2048`) → `pow_nine_lt_of_lt` (`w⁹ < 2^4608`);
    `two_pow_pow_three_pow_eq` → `two_pow_pow_eight_pow_eq` (`(2^w^8)^(k*w) = 2^(k*w^9)`).
- `Size/Constants/FormalMultiple.lean`: `four_mul_lt_of` (`n < 2^2^4613 → 4m < 2^2^4617`),
  `cstar_lt` (`cstar < 2 ^ 2 ^ 4617`, was `2059`), `formal_multiple_size` (same numeral).
- `Size/Constants/T.lean`:
  - **renamed** `W_pow_three_lt` (`W^3 < 2^1536`) → `W_pow_eight_lt` (`W ^ 8 < 2 ^ 4096`);
  - **new** `Hmax_lt_two_pow_two_pow : CatalogueBound8 → Hmax < 2 ^ W ^ 8 ∧ 2 ^ W ^ 8 < 2 ^ 2 ^ 4096`
    (the plan's `H_max < 2^(W^8) < 2^(2^4096)`);
  - `Hmax_lt_D`, `cstar_lt_D`, `R_eq_D`, `r_equals_d`, `Q_eq_closed`, `Ccm_lt_Q17`, `max_Aht_eq`,
    `Aht_eq_closed`, `T_eq_closed`, `t_identity`, `T_lt`, `T_lt_triplePower`: only the hypothesis
    type changed (statements identical; `R = D` still holds since `4096, 4617 ≤ 8008`).
- `Size/Constants/Cutoff.lean`: `literal_cutoff` — hypothesis type only.
- `Size/Constants/Closed.lean`: `closed_comparisons_1` is now
  `433 + 22 * 2 ^ 4608 < 2 ^ 4613 ∧ 4 + 1262628 + 16104 * 2 ^ 4608 < 2 ^ 4623 ∧ 1262628 = 433 * 2916 ∧ 16104 = 22 * 732`
  (was `2^2048`, `2^2053`, `2^2063`); `closed_comparisons_2` is now `2 + 10 * 2 ^ 4613 < 2 ^ 4617`
  (was `2 + 10 * 2^2054 < 2^2059`); `closed_comparisons` updated accordingly. Decided by the kernel
  with `exponentiation.threshold 4700`. The old items were replaced in place, not kept, as nothing
  else used them.
- `Size/Majorants/Cutoff.lean`: `admissible_cutoff` — hypothesis type; inside, the psi-index bound
  is now `|n| + 1 ≤ 2^(2^4618) < T` (was `2^(2^2060)`); module doc updated.
- `Size/Majorants/Bound.lean`: `PstarNat_maj`, `Pstar_degree_coeff`, `Pstar_size`,
  `Pstar_target_bounds` — hypothesis type only.

The old `CatalogueBound` and `cataloguePrime_lt_of_catalogueBound` remain in PrimePattern.lean.

## Statement corrections

None: the constants are the plan's (`X = 2^(W^8)`, `H_max < 2^(W^8) < 2^(2^4096)`,
`1 ≤ H_cat ≤ (2^(W^8))^(22W)`, `N_s < 2^(2^4613)`, `ℓ < 2^(2^4623)`, `c_* < 2^(2^4617)`).

## Problems

- In `catalogueBound8_of_catalogueBound`, the step `2^(W³) ≤ 2^(W⁸)` made the kernel try to
  evaluate `Nat.pow` on closed powers of `W` (the power-instance mismatch between core
  `Nat.pow_le_pow_right` and Mathlib's `Monoid.npow`). Proving it for a variable `w ≥ 1` with
  `pow_le_pow_right₀` and then instantiating fixed it.

## Suggestions for the next agent

- The analytic tasks need to deliver exactly `ZInQ.CatalogueBound8`. Since `Progressions/` modules
  may import only Mathlib, the final instance can either import `ZInQKernel.Hypotheses.PrimePattern`
  (which is Mathlib-only itself) or prove a Mathlib-only statement about `4 * primorial 324` that
  is then unfolded into `CatalogueBound8`.
- Once `CatalogueBound8` is a theorem, drop `hCAT` from `Pstar_spec_of`, `Pstar_spec`,
  `assembly` and the three main theorems, and remove the `_catalogueBound` corollary (or keep it as
  a trivial wrapper).
- The blueprint's size articles (`size/constants/catalogue-bounds.md`, `catalogue-size.md`,
  `formal-multiple-size.md`, `r-equals-d.md`, `closed-comparisons.md`, `size/majorants/admissible-cutoff.md`,
  `main/catalogue-bound.md`) still state the `W³` cutoff and the old numerals.
