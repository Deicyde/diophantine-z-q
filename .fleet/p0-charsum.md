# p0-charsum report: file 6 of nt-prop0.md §4.1 (CharSum.lean)

Everything is in `ZInQKernel/RouteK/Selmer/CharSum.lean` (457 lines), namespace
`ZInQ.RouteK.Selmer`. The root module is `ZInQKernel/RouteK/SelmerCharSum.lean`, imported from
`ZInQKernel.lean`. `lake build ZInQKernel` succeeds, with no `sorry` and no `native_decide`. The file
compiles in about 8 s; the `decide +kernel` checker finishes almost at once. `#print axioms` on
`exists_xi`, `exists_xi_of_card`, `eight_mul_fibreCard_ge` and `cubicCharSum_sq_le` shows only
`propext`, `Classical.choice` and `Quot.sound`.

## Leaves

There are no blueprint articles; the leaves come from nt-prop0.md §2.3 and §4.2.

| article path | Lean name | status |
| --- | --- | --- |
| nt-prop0 §2.3, Lemma Q | `sum_quadraticChar_mul_sub` | proved |
| nt-prop0 §2.3, Lemma J, `S(1)² ≤ 4q` | `cubicCharSum_one_sq_le` | proved |
| nt-prop0 §2.3, Lemma J, the form the count uses: `S(d²)² ≤ 4q` for `d ≠ 0` | `cubicCharSum_sq_le` | proved |
| nt-prop0 §2.3, Jacobsthal identity (3) | `sum_cubicCharSum_sq` | proved |
| nt-prop0 §2.3, step 2 count `8N ≥ q − 15 − |S(d²)|` | `eight_mul_fibreCard_ge` (with `N = fibreCard d α β`) | proved |
| nt-prop0 §2.3, step 1, `p ≥ 29` | `exists_xi_of_card` (any finite field, `q ≥ 26`) | proved |
| nt-prop0 §2.3, step 3, `p < 29` | `xiCheck_small` (`decide +kernel`), `exists_xi_of_check` | proved |
| nt-prop0 §2.3, step 1 | `exists_xi` | proved |

Statement of the main result:

```lean
theorem exists_xi {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {d a b : ZMod p}
    (hd : d ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0) :
    (IsSquare a ∧ IsSquare b) ∨
      ∃ ξ : ZMod p, IsSquare (ξ / a) ∧ IsSquare ((ξ - d) / b) ∧ IsSquare ((ξ + d) / (a * b))
```

As in the note, the squares may be zero. For the lift in Good.lean, the stronger
`exists_xi_of_card` also gives `ξ ∉ {0, d, −d}` (for `p ≥ 29`, or any `𝔽_q` with `q ≥ 26`).

## Statement corrections and deviations from the note

- No mathematical corrections. Lemmas Q and J and the count are stated over any finite field `F` with
  `ringChar F ≠ 2` (`q = Fintype.card F`), with `χ = quadraticChar F : MulChar F ℤ`. They are
  specialised to `ZMod p` only in `exists_xi`.
- **Lemma J, simpler route.** The proof needs no non-square `g` and no split by `p mod 4`. Grouping
  by fibres of `t ↦ t²`, which have `1 + χ(n)` elements (`quadraticChar_card_sqrts`), gives
  `(q − 1) S(1)² = Σ_t S(t²)² = Σ_n (1 + χ n) S(n)² ≤ 2 Σ_n S(n)² = 2q(q − 1)(1 + χ(−1)) ≤ 4q(q − 1)`.
  Lemma J takes about 170 lines (target: about 300).
- **The count.** The excluded points are not handled term by term. Instead,
  `Σ_{ξ ∉ {0,±d}} P = Σ_F P − Σ_{excluded} P`, where `Σ_F P = q − αβ − α − β + S(d²)` (Lemma Q and
  `Σ χ(ξ − e) = 0`). At each excluded point one factor of `P` is 1 and the other two lie in `[0, 2]`,
  so `P ≤ 4` there. That gives the same constant, 15. The positivity threshold is `q ≥ 26`, since
  `(q − 15)² > 4q` when `q > 25`. The note uses 29 because it treats only primes.
- **Small primes.** The checker covers `d̄ ∈ 𝔽_p*` and the three nontrivial pairs of classes.
  Classes are encoded on ℕ as `1` or `p − 1`, the value of Euler's `x^((p−1)/2) mod p`, with
  `Nat.pow` written explicitly so that the kernel computes it with GMP. The bridge to `ZMod p` uses
  `ZMod.euler_criterion` and `ZMod.pow_div_two_eq_neg_one_or_one`. The trivial pair `(1, 1)` goes to
  the first disjunct. That also covers the pairs that need the trivial class (see `t_fp_surj.py`).

## Lemmas added beyond the leaves (all in `ZInQ.RouteK.Selmer`)

`sum_quadraticChar_sub_sq`, `quadraticChar_pow_three`, `quadraticChar_abs_le_one`, `cubicCharSum`
(def), `cubicCharSum_mul_sq` (`S(nt²) = χ(t) S(n)`), `cubicCharSum_zero`,
`sum_quadraticChar_sq_sub`, `sum_quadraticChar_mul_sq_eq`, `sum_cubicCharSum_sq_comp_sq_le`,
`sum_quadraticChar_sub`, `one_add_mul_quadraticChar_mem`, `one_add_mul_quadraticChar_eq`,
`fibreCard` (def), `fibreCard_pos`, `isSquare_div_of_quadraticChar_eq`, `eulerNat`, `xiOK`,
`xiCheckPrime`, `xiSmallPrimes` (defs), `eulerNat_cast`, `isSquare_div_of_pow_eq`, `xi_of_xiOK`,
`exists_classNat`.

## Problems

None in the mathematics.

## Suggestions for the next agent (Good.lean)

- Use `exists_xi` for Lemma G2. Apply it to the reductions `ā, b̄, d̄ ∈ ZMod p` (nonzero because
  `p ∤ abd`). If the first disjunct holds, lift with SQ(a). Otherwise take `x ∈ ℤ` with `x̄ = ξ`; if
  `ξ ∈ {0, ±d̄}`, take `x ∈ {0, ±d}` exactly, as in §2.3. To skip the case split for `p ≥ 29`, use
  `exists_xi_of_card`, which gives `ξ ∉ {0, ±d̄}`.
- `isSquare_div_of_quadraticChar_eq` and `isSquare_div_of_pow_eq` turn character conditions into
  `IsSquare` on quotients. They may be useful in other files.
