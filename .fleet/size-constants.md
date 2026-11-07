# Report: size-constants

Modules: `ZInQKernel/Size/Constants/*.lean`, root `ZInQKernel/Size/Constants.lean`
(imported from `ZInQKernel.lean`). Namespace `ZInQ.Size`. `lake build ZInQKernel` succeeds.
No `axiom`, `native_decide`, kernel-skipping options or `sorry`. Branch `wip/size-formal`
(the formal-multiple existence) is merged. `#print axioms` gives `propext, Classical.choice,
Quot.sound` for every leaf (`closed_comparisons`: `propext` only).

## Leaves

| Article | Lean name | Status |
| --- | --- | --- |
| size/constants/small-constant-bounds.md | `ZInQ.Size.small_constant_bounds` (parts `Ps_lt`, `W_gt`, `W_lt`, `W_lt_two_pow_512`, `F_bounds`, `G0_lt`) | proved |
| size/constants/closed-comparisons.md | `ZInQ.Size.closed_comparisons` (items `closed_comparisons_1` … `_7`) | proved |
| size/constants/catalogue-bounds.md | `ZInQ.Size.catalogue_bounds` (parts `cataloguePrime_bounds`, `Hmax_lt`, `Hcat_bounds`) | proved |
| size/constants/catalogue-size.md | `ZInQ.Size.catalogue_size` (parts `Ns_bounds`, `ell_lt`) | proved |
| size/constants/d-bounds.md | `ZInQ.Size.D_bounds` | proved |
| size/constants/formal-multiple-size.md | `ZInQ.Size.formal_multiple_size` (parts `M0_bounds`, `cstar_lt`) | proved (uses size-formal's `M0_bounds`) |
| size/constants/r-equals-d.md | `ZInQ.Size.r_equals_d`, `ZInQ.Size.R_eq_D` | proved |
| size/constants/t-identity.md | `ZInQ.Size.t_identity` (parts `Q_eq_closed`, `Ccm_lt_Q17`, `max_Aht_eq`, `Aht_eq_closed`, `T_eq_closed`) | proved |
| size/constants/t-bound.md | `ZInQ.Size.closedT_lt` | proved (no hypothesis, no `sorry`) |
| size/cutoff.md | `ZInQ.Size.literal_cutoff`, `ZInQ.Size.formal_multiple_succeeds` | proved (uses size-formal's `M0_bounds`) |

The formal-multiple input is size-formal's `ZInQ.Size.M0_bounds (h : 1 ≤ Ns)` (from
`exists_formal_multiple`), applied with `Syntax.Ns_pos`. While size-formal was still running, a
`sorry` placeholder stood in for it; the placeholder is removed now that the branch is merged.

## Statement corrections and precisions

- catalogue-bounds: Lean counts catalogue primes from 0, as `Syntax.cataloguePrime` does:
  `cataloguePrime W 324 r j` for `j < 22` is the blueprint's `p_{r,j+1}`.
- formal-multiple-size: `1 ≤ M₀ ≤ N_s^10` (`M0_bounds Ns_pos`) needs no catalogue bound:
  `N_s ≥ 1` is `Syntax.Ns_pos`, which follows from Dirichlet's theorem. Only `c_* < 2^(2^2059)` uses CAT.
  `formal_multiple_size` still takes `hCAT`, as the article does.
- cutoff: the formal-multiple part is stated separately as `formal_multiple_succeeds`, with no
  hypothesis, as the article's last paragraph says. `literal_cutoff hCAT` includes it as well.
  Item 2 is split into its equations: `T = (48 A_ht)^13`, `T = (96·10^13)^13 D^(2210 G₀² D³)`,
  `A_ht = 2·10^13 max(1, C_cm, Q^17)`, `A_ht = 2·10^13 Q^17`, `Q = R^(R E₀)` and
  `Q = D^(10 G₀² D³)`. The maximum is written `max (max 1 Ccm) (Q ^ 17)`, as in `Syntax.Aht_eq`.
- closed-comparisons item 7 is stated as `max (max (max 6564 4640) 123720) 87483 < 2 ^ 17`.
- t-bound: the variable form `closedT_lt_of` also needs `0 < g`. With `g = 0` the exponent is 0,
  so `D^(2210 g² D³) < 2^(D^5)` would be `1 < 2^(D^5)`, which still holds, but the proof's step
  `D^E < (2^D)^E` needs `E ≠ 0`. `G₀ > 0`, so the article's statement is unaffected.
- t-identity: the proof uses only `D ≥ 300`, `G₀ ≥ 1` and `D ≥ 1`, as the article says.

## Lemmas added beyond the leaves

- `ZInQ.Size.AmbientPow.*` (`Pow.lean`): `natPow_lt_natPow_right/left`, `natPow_le_natPow_right/left`,
  `lt_two_natPow`, `natPow_pos`, `natPow_add`, `natPow_mul`, `mul_natPow`, `le_self_natPow`,
  `one_le_natPow` and `prod_le_natPow_card`. These are the core and Mathlib power lemmas restated
  with the ambient instance (see Problems).
- Variable forms of every estimate: `D_bounds_of`, `mul_lt_of_catalogue`, `ell_lt_of_catalogue`,
  `four_mul_lt_of`, `Ccm_lt_of`, `two_pow_lt_Q17_of`, `Q_exponent_eq`, `Aht_closed_of`,
  `T_closed_of`, `closedT_lt_of`, `max_three_eq_of`, `max_one_eq_of`, `pow_four_lt_of_lt`,
  `two_pow_pow_three_pow_eq`.
- Facts about the constants: `D_gt`, `D_lt`, `two_pow_two_pow_lt_D` (`2^(2^k) < D` for `k ≤ 8008`),
  `lt_D_of_lt`, `three_hundred_le_D`, `W_pow_three_lt`, `Hmax_lt_D`, `cstar_lt_D`,
  `ten_pow_twelve_lt_D`, `T_lt` (`T < 2^(2^(2^9013))`),
  `triplePower_eq` and `T_lt_triplePower` (`T < NumericalTowerBounds.triplePower 9013`, the form
  used by upstream's tower comparisons).

## Problems

- The power instances. With Mathlib imported, `a ^ n` on `ℕ` elaborates as
  `Monoid.toNPow Nat.instMonoid`. Core `Nat.pow_*` lemmas use `instPowNat`, and generic Mathlib
  lemmas such as `Finset.prod_le_pow_card` and `pow_lt_pow_right₀` use other instance paths.
  `HPow.hPow` is a projection with `abbrev` hints, so when the kernel compares two power terms that
  differ only in the instance, it unfolds both sides instead of comparing arguments. It reaches
  `Nat.pow 2 X`, tries GMP evaluation, and fails with "the kernel refused to evaluate `Nat.pow`" as
  soon as `X` reduces to a huge literal (`W^3`, `2^8008`, …). The kernel ignores
  `@[irreducible]`, so `W`, `D`, `Hcat` and the rest are unfolded too. The fix used throughout:
  (1) prove every estimate for variables, where instance mismatches are harmless; (2) apply the
  lemmas to closed terms only through the `AmbientPow` wrappers, whose statements use the ambient
  instance; (3) bring the named constants in by `rw [X_eq]; exact generic_lemma …`, so the kernel
  only sees syntactically equal terms. Closed literal identities between powers are proved with
  `congrArg (2 ^ ·) (h : e₁ = e₂)`, where `h` is an equation between small exponents.
- `max`: the bounds for `R` and `A_ht` go through variable lemmas (`max_three_eq_of`,
  `max_one_eq_of`), never `rw [max_eq_left]` on the constants, for the same reason.

## Suggestions for the next agent

- Consumers that need `T < triplePower 9013` should use `T_lt_triplePower`. Do not `show` or
  `unfold` `triplePower 9013`: upstream states it with another power instance.
- Other size tasks that work with the big constants can import `ZInQKernel.Size.Constants.Pow` and
  `open ZInQ.Size.AmbientPow`.
