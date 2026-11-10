# pd-lean-1 report: Proposition D, files 1–2 (CharSum, Description)

Every leaf is proved. `lake build ZInQKernel` succeeds. There is no `sorry`, `axiom` or
`native_decide`. `#print axioms` on `goodSlopePrime_of_gcd`, `goodSlopePrime_iff`,
`goodSlopePrime_seventeen'`, `jacobsthal` and `mod_four_of_dvd_cp` reports
`[propext, Classical.choice, Quot.sound]`. Everything is in namespace `ZInQ.Density`. The files are
`ZInQKernel/Density/CharSum.lean` and `ZInQKernel/Density/Description.lean`, with root module
`ZInQKernel/DensityCM.lean`, imported from `ZInQKernel.lean`.

## Leaves

Article paths refer to `docs/research/pd-paper.md` (there is no blueprint leaf list for this task).

| article (pd-paper.md) | Lean name | status |
| --- | --- | --- |
| §1.2 notation `φ_p(a)` | `jac` (def), `jac_eq_cubicCharSum` | proved |
| Lemma 1.1 (point count) | `pointCount_eq` | proved |
| Lemma 1.2 (scaling) | `jac_sq_mul` | proved |
| Lemma 1.3 (shifted products) | `sum_quadraticChar_shift_mul`, `sum_quadraticChar_shift_mul_self` | proved |
| Lemma 1.4 (Jacobsthal), second moment | `sum_jac_sq`, `jacobsthal` | proved |
| Lemma 1.4 (evenness) | `jac_even` | proved |
| Lemma 1.5 (divisibility by 4) | `four_dvd_pointCount`, `four_dvd_pointCount_of_mod_four` | proved |
| §1.3 class, `c_p` | `InClass` (def, decidable), `cp` (def), `cp_eq`, `jac_one_eq` | proved |
| Prop 1.6 (1) | `cp_odd`, `sq_add_sq_of_nonsquare`, `exists_sq_add_sq` | proved |
| Prop 1.6 (2) | `pointCount_pair` (also `quadraticChar_seven`, `d_mul_dbar`) | proved |
| Prop 1.6 (3) | `gcd_pointCount_eq` | proved |
| Prop 1.6 (4) | `goodSlopePrime_of_gcd`, `goodSlopePrime_iff`, `mod_four_of_dvd_cp` | proved |
| §6.5 success criterion | `inClass_seventeen`, `cp_seventeen` (`cp 17 = -1`), `goodSlopePrime_seventeen'` | proved |

## Statement corrections and changes

1. `sum_quadraticChar_shift_mul` takes `hp2 : p ≠ 2`. The §6.1 statement is false for `p = 2`; this is
   the referee's finding F1.
2. `four_dvd_pointCount` takes only `hp2 : p ≠ 2`, not `p % 4 = 1`. This is stronger than Lemma 1.5.
   For `p ≡ 3 (mod 4)` the involution `x ↦ −D²/x` has no fixed points. For `p ≡ 1 (mod 4)` its
   fixed points in `X` are closed under `x ↦ −x`, because `χ(−1) = 1` follows from `x² = −D²`. So
   the proof never needs the explicit `±iD`. The note's form is `four_dvd_pointCount_of_mod_four`.
3. `jac_even` holds for every odd `p`. Lemma 1.4 states evenness only for `p ≡ 1 (mod 4)`.
4. `cp : ℕ → ℤ` is defined for every `p`: it is `jac 1 / 2` when `p` is prime and `0` otherwise.
   `cp_eq` unfolds it under `[Fact p.Prime]`. No `ep` definition was added. Instead
   `sq_add_sq_of_nonsquare` gives `p = cp p² + (jac r₀ / 2)²` for every non-square `r₀`, and
   `exists_sq_add_sq` gives the existential form.
5. `goodSlopePrime_iff` (both directions of Prop. 1.6 (4), for class primes) is added. The note uses
   only the direction "⇐".

## Lemmas added beyond the leaves

- `card_mod_two_eq_card_fixed`: an involution on a finset satisfies `#s ≡ #Fix (mod 2)`. It is proved
  with `Finset.sum_involution` in `ZMod 2`.
- `sum_eq_two_mul_card_sub`: a sum of values in `{−1, 0, 1}` equals `2#{f = 1} − #{f ≠ 0}`.
- `ringChar_zmod_ne_two`, `quadraticChar_zmod_mem`, `jac_zero`.
- `int_gcd_sub_add_two_mul`: for `c` odd and `n ≡ 2 (mod 4)`, `gcd(n − 2c, n + 2c) = 4 gcd(c, n)`.
  `nat_gcd_eq_of_sub_add` is the same statement for `ℕ` values in either order.
- `InClass.mod_four`, `InClass.ne_two`, `InClass.ne_seven`, `seven_ne_zero`,
  `not_isSquare_{three,five,six}_zmod_seven`, `pointCount_seventeen_one`.

## Reuse

The second moment `Σ_a φ(a)² = p(p − 1)(1 + χ(−1))` and the scaling come from
`ZInQ.RouteK.Selmer.sum_cubicCharSum_sq` and `cubicCharSum_mul_sq`, via `jac a = cubicCharSum (−a)`.
Lemma 1.3 comes from `sum_quadraticChar_mul_sub`. `ZInQKernel/RouteK/Selmer/CharSum.lean` is imported
unchanged.

## Problems

None. The finite check for `p = 17` is a `decide` over 289 pairs (`pointCount 17 1 = 16`), which the
kernel checks quickly. The check `cp 41 = −5` suggested in §6.2 was not added; it would need a
`decide` over 1681 pairs and is not required.

## Suggestions for the next agent (files 3–9)

- State `BadSet` with `InClass` and `cp` exactly as in §6.1. `mod_four_of_dvd_cp` has exactly the
  §6.1 signature.
- For `G*_L ⊆ G`, use `goodSlopePrime_of_gcd`. A prime with no prime factor of `gcd(cp p, p + 1)`
  has `Int.gcd = 1`, and `mod_four_of_dvd_cp` restricts the odd prime factors to `ℓ ≡ 1 (mod 4)`.
  The prime `2` never divides, because `cp_odd` makes the gcd odd.
- Use `exists_sq_add_sq` (`p = c² + e²`) for the lattice and sieve parametrisation in files 6 and 8.
