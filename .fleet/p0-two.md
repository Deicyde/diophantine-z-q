# p0-two: Proposition 0, file 5 (the place 2, Lemma T)

Plan: `docs/research/nt-prop0.md` §2.5 and §4.1 file 5. Namespace `ZInQ.RouteK.Selmer`. File
`ZInQKernel/RouteK/Selmer/Two.lean` (401 lines). Root module `ZInQKernel/RouteK/SelmerTwo.lean`,
imported from `ZInQKernel.lean`. Branch base: origin/main + origin/wip/p0-local +
origin/wip/p0-charsum (both merged cleanly).

`lake build ZInQKernel` succeeds. There is no `sorry`, `native_decide` or `axiom`. `#print axioms` on
`loc_two_adic_iff` and on `loc_two_adic_iff_of_odd` shows only `propext`, `Classical.choice` and
`Quot.sound`.

## Leaves

| Article (nt-prop0 section) | Lean name | Status |
| --- | --- | --- |
| §2.5 Lemma T, for `d ≡ 5 (mod 8)` | `loc_two_adic_iff` | proved |
| §2.5 Lemma T, for every odd `d` (the general form) | `loc_two_adic_iff_of_odd` | proved |
| §2.5 table, rows with `k = 1` (the four non-torsion witnesses) | `loc_two_adic_five` | proved |

Statement, in the shape of `loc_padic_dvd_iff`:

```lean
theorem loc_two_adic_iff {d : ℕ} (hd8 : d % 8 = 5) (a b : ℤ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Loc ℚ_[2] d a b ↔ ∃ i j k : ℕ, i < 2 ∧ j < 2 ∧ k < 2 ∧
      IsSquare ((a * d ^ i * (-1) ^ j : ℤ) : ℚ_[2]) ∧
      IsSquare ((b * 2 ^ i * (-d) ^ j * 5 ^ k : ℤ) : ℚ_[2])
```

`loc_two_adic_iff_of_odd` is the same statement with `(hd : Odd d)` in place of `hd8`.

## Statement corrections

- **The note's statement is correct.** The note's hypotheses are stronger than needed, though.
  Neither `d ≡ 5 (mod 8)` nor squarefreeness is used: the proof needs only that `d` is odd, i.e. that
  `‖d‖₂ = 1`. (The witnesses need `1 ± 4d ≡ 5 (mod 8)`, which holds for every odd `d`. In the
  `v = 0` case, `x ≡ ±d` holds for any odd `d`.) So the general theorem is `loc_two_adic_iff_of_odd`,
  and `loc_two_adic_iff` is its corollary with the note's `d % 8 = 5`. I left out `Squarefree d`,
  because it would be an unused hypothesis. For `d ≢ 5 (mod 8)` the eight classes may coincide in
  pairs, but the statement stays true as written.
- **The case analysis on `v = v₂(x)` differs a little from the note.**
  - `v ≤ −3` is handled together, since (P) needs only `‖d‖ ≤ ‖x‖/8`. The note splits off `v ≤ −4`
    and excludes `v = −3` by parity.
  - Likewise `v ≥ 3`.
  - Only `v = ±1` uses the odd-norm contradiction.
  - In the `v = 0` case, the note's step "the other has valuation odd and at least 3" is done with
    norms. One of `x ∓ d` has norm exactly `1/2`, since both are `< 1` and their difference `2d`
    has norm `1/2`. The other has norm `≤ 1/4` by discreteness, `≠ 1/4` by the parity of the
    product's norm, and so `≤ 1/8`.
  - "`s ≡ ∓d (mod 4)`, so `≡ ∓d` or `∓5d`" becomes `sqEq_add_or_five_two_adic`.

## Lemmas added beyond the leaves (all in `ZInQ.RouteK.Selmer`, file `Selmer/Two.lean`)

- `two_adic_norm_eq_zpow`: `‖z‖ = 2^(−v(z))` with a real base `2`.
- `two_adic_norm_le_of_lt`: discreteness, `‖z‖ < 2^k → ‖z‖ ≤ 2^(k−1)`.
- `two_adic_norm_intCast_of_odd`, `two_adic_norm_natCast_of_odd`, `two_adic_norm_four`,
  `two_adic_norm_five`.
- `two_adic_norm_one_add_lt`: `‖t‖ = 1 → ‖1 + t‖ < 1`, via `toZMod` into `ZMod 2`.
- `two_adic_norm_add_lt`: two elements of the same nonzero norm have a sum of smaller norm. This
  is the only "mod 2" input. Residues mod 8 never appear explicitly.
- `sqEq_add_two_adic`: (P) at 2 in the sharp form `‖y‖ < ‖x‖/4`.
- `sqEq_add_or_five_two_adic`: `‖y‖ ≤ ‖x‖/4` gives `x + y ≡ x` or `x + y ≡ 5x`.
- `SqEq.trans_eq`: rewrite the right-hand class by an equation, usually closed by `ring`.
- `sqEq_one_of_isSquare`: a nonzero square is `≡ 1`.

I grepped all names against `ZInQKernel/`, `lean/ZInQ/` and the current origin/wip/p0-good and
origin/wip/p0-bits. None collides. `SqEq.trans_eq` and `sqEq_one_of_isSquare` are generic over a
field and could later move to `Covering.lean`.

## Cost figures

- `Selmer/Two.lean` has 401 lines, against the note's estimate of 600–1,000 for file 5.
  - About 100 lines of helpers.
  - About 70 lines for the witnesses.
  - About 230 lines for Lemma T itself.
- **Speed.** I compiled with `-DElab.async=false -Dprofiler=true -Dprofiler.threshold=100`. No
  declaration reaches 100 ms. The whole file takes about 6 s after the 3.3 s import. Tactic time is
  dominated by typeclass inference (1.0 s total) and `norm_num` (0.4 s total). The slowest
  declaration is `loc_two_adic_iff_of_odd`, which takes the bulk of the 6 s; that is still far under
  the 30 s criterion.
- Five edit–compile rounds.

## Problems

None in the mathematics. Two Lean notes:
- `field_simp` normalises `1 - 4 * d` to `1 - d * 4`. Nonzero hypotheses must be supplied in
  that orientation as well, or it leaves inverses behind.
- `padic_norm_ne_zpow_odd` lives in `BadOdd.lean`, so `Two.lean` imports `BadOdd`, not just
  `PadicSquare`.

## Suggestions for the next agent

- **File 8 (`Bits.lean`, `twoAdicRows 5`).** Use `loc_two_adic_iff` (or `_of_odd`). Its right-hand
  side is "`a ≡ d^i(−1)^j` and `b ≡ 2^i(−d)^j 5^k`" in `ℚ₂*/ℚ₂*²`. To turn it into bits of
  `a(σ)`, `b(σ)`, use `isSquare_two_adic_iff` or `isSquare_intCast_div_two_adic` on the integers
  `a d^i (−1)^j` and `b 2^i (−d)^j 5^k`: their 2-adic valuation must be even, and the odd part must
  be `≡ 1 (mod 8)`.
- **File 9 (`Prop0.lean`).** At `p = 2`, `Sel2` membership is `loc_two_adic_iff` with the casts
  exactly as in the `Sel2` definition: `(d : ℚ_[2])` with `d : ℕ` and `(a : ℚ_[2])` with `a : ℤ`.
- `two_adic_norm_add_lt` and `sqEq_add_or_five_two_adic` are the convenient interface for any
  further 2-adic case analysis.
