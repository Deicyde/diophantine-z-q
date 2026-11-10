# p0-good: Proposition 0, file 7 (Good.lean, odd primes not dividing `d`)

Plan: `docs/research/nt-prop0.md` §2.3 and §4.1 file 7. Module `ZInQKernel/RouteK/Selmer/Good.lean`
(185 lines), namespace `ZInQ.RouteK.Selmer`. Root module `ZInQKernel/RouteK/SelmerGood.lean`,
imported from `ZInQKernel.lean`. This branch also contains the merges of `wip/p0-local` and
`wip/p0-charsum`.

`lake build ZInQKernel` succeeds. There is no `sorry` and no `native_decide`. `#print axioms` on
`loc_padic_good_even`, `loc_padic_good_of_units` and `loc_padic_good_iff` shows only `propext`,
`Classical.choice` and `Quot.sound`. The file compiles in about 5 s.

## Leaves

| article path | Lean name | status |
| --- | --- | --- |
| nt-prop0 §2.3, Lemma G1 | `loc_padic_good_even` | proved |
| nt-prop0 §2.3, Lemma G2 | `loc_padic_good_of_units` | proved |
| nt-prop0 §2.3, combined form for the assembly | `loc_padic_good_iff` | proved |

Statements (`variable {p : ℕ} [Fact p.Prime]`):

```lean
theorem loc_padic_good_even (hp2 : p ≠ 2) {d : ℕ} (hpd : ¬p ∣ d) {a b : ℤ} (ha : a ≠ 0)
    (hb : b ≠ 0) (h : Loc ℚ_[p] d a b) : Even (padicValInt p a) ∧ Even (padicValInt p b)

theorem loc_padic_good_of_units (hp2 : p ≠ 2) {d : ℕ} (hpd : ¬p ∣ d) {a b : ℤ}
    (ha : ¬(p : ℤ) ∣ a) (hb : ¬(p : ℤ) ∣ b) : Loc ℚ_[p] d a b

theorem loc_padic_good_iff (hp2 : p ≠ 2) {d : ℕ} (hpd : ¬p ∣ d) {a b : ℤ} (ha : Squarefree a)
    (hb : Squarefree b) : Loc ℚ_[p] d a b ↔ ¬(p : ℤ) ∣ a ∧ ¬(p : ℤ) ∣ b
```

## Statement corrections

- **G1 needs `a, b ≠ 0`.** The note omits this. With `a = 0`, `Loc` holds for every `b` (take
  `x = d`: `x/0 = 0`, `0/b = 0` and `(2d)/0 = 0` are all squares). Since `padicValInt p 0 = 0`,
  `v_p(b)` could then be odd. Squarefree `a, b` are nonzero, so `loc_padic_good_iff` needs no
  extra hypothesis.
- `d : ℕ` and `a b : ℤ` are casts into `ℚ_[p]`, matching `Sel2` and `loc_padic_dvd_iff`.
  `d ≠ 0` follows from `p ∤ d`. G2 needs no squarefreeness.

## Proofs

- **G1.** It is enough to show that `a` and `b` lie in the square classes of units of `ℤ_p`
  (`even_valuation_of_sqEq_unit`). The first alternative and the three torsion witnesses
  (`loc_torsion`) give this at once. In the generic case, compare `‖x‖` with `‖d‖ = 1`, as in
  Lemma B, using (P) (`sqEq_add_of_norm_lt`):
  - if `‖x‖ > 1`, then `(a, b) ≡ (1, 1)`;
  - if `‖x‖ < 1`, then `b ≡ −d` and `a ≡ −d²`;
  - if `‖x‖ = 1`, then `a ≡ x`, and `b ≡ x − d` or `b ≡ (x + d)x`, depending on which of `x ∓ d`
    is a unit. They are not both non-units, since `‖2d‖ = 1`.
- **G2.** Apply `exists_xi` to `d̄, ā, b̄`. If `ā` and `b̄` are squares, lift both by
  `isSquare_intCast_of_residue`. Otherwise take the integer lift `x` of `ξ`, with `x = 0`, `d` or
  `−d` exactly when `ξ = 0`, `d̄` or `−d̄`. Then each of `x`, `x − d`, `x + d` is either `0` or prime
  to `p`, and `isSquare_padic_div_of_zmod` lifts each quotient. I used `exists_xi` alone, with no
  split at `p ≥ 29`.
- **Combined.** (⇐) is G2. For (⇒), G1 gives an even valuation, and a squarefree integer has
  valuation at most 1, so it is prime to `p`.

## Lemmas added beyond the leaves (all new names, grepped against `ZInQKernel/`)

- `even_valuation_of_sqEq_unit`: `‖u‖ = 1` and `A ≡ u` imply `Even A.valuation`.
- `isSquare_padic_div_of_zmod`: if `p ∤ n`, `m = 0 ∨ p ∤ m`, and `m̄/n̄` is a square in `ZMod p`,
  then `m/n` is a square in `ℚ_p`. This is (RT) in the quotient form that `exists_xi` produces.
- `not_dvd_of_squarefree_of_even_padicValInt`.

## Problems

None. The worktree had no `.lake`, so I copied it (and `lean/.lake`) from the main clone with
`cp --reflink`, as p0-local did.

## Suggestions for the next agent

- File 9 (`Prop0.lean`): at a prime `p ∤ 2d`, use `loc_padic_good_iff` directly. For the "onto"
  half (`Sel2 d ⊆ range (selPair d)`) it gives `p ∤ a` and `p ∤ b`, so a Selmer `a` or `b` is ±
  a power of 2 times divisors of `d`. For the iff, every `selPair` value is a product of `−1`, `2`
  and primes dividing `d`, so `loc_padic_good_of_units` covers all good primes at once.
