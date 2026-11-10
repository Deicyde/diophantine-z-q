# p0-assembly: Proposition 0 (file 9 of nt-prop0 §4.1) and the CR₃^Sel main theorem

Branch base: origin/main plus the merges of origin/wip/p0-bits (which contains p0-local,
p0-charsum and p0-two) and origin/wip/p0-good. Both merged without conflicts.
- New file: `ZInQKernel/RouteK/Selmer/Prop0.lean` (about 115 lines, namespace
  `ZInQ.RouteK.Selmer`).
- Root module: `ZInQKernel/RouteK/SelmerProp0.lean`, imported from `ZInQKernel.lean`.
- `ZInQKernel/Main.lean`: one new theorem and one new import.

Checks:
- `lake build ZInQKernel` succeeds.
- `scripts/check_target.py` passes.
- There is no `sorry`, `native_decide` or `axiom`.
- `#print axioms` shows only `propext`, `Classical.choice` and `Quot.sound` on `prop0`,
  `sel2_subset_range_selPair`, `prop0Statement`, `certifiedRank_of_certifiedRankSel` and
  `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel`.

## Leaves

| article path | Lean name | status |
| --- | --- | --- |
| nt-prop0 §2.7, Proposition 0 (the iff) | `ZInQ.RouteK.Selmer.prop0` | proved |
| nt-prop0 §2.7, onto half | `ZInQ.RouteK.Selmer.sel2_subset_range_selPair` | proved |
| nt-prop0 §1.4, `Prop0Statement` | `ZInQ.RouteK.Selmer.prop0Statement` | proved |
| nt-prop0 §1.4, CR₃^Sel → CR₃ | `ZInQ.RouteK.Selmer.certifiedRank_of_certifiedRankSel` | proved |
| Main theorem with CR₃^Sel | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel` | proved |

Statements:

```lean
theorem prop0 {d : ℕ} (hd5 : d % 8 = 5) (hsq : Squarefree d) (σ : Unknowns d.primeFactors) :
    (natConfig d (odd_of_mod_eight_eq_five hd5)).IsSol σ ↔ selPair d σ ∈ Sel2 d
theorem sel2_subset_range_selPair {d : ℕ} (hd : Odd d) : Sel2 d ⊆ Set.range (selPair d)
theorem prop0Statement : Prop0Statement
theorem certifiedRank_of_certifiedRankSel (hCRS : CertifiedRankSel) : CertifiedRank
theorem ZInQ.exists_bounded_integer_polynomial_defining_integers_of_certifiedRankSel
    (hH : SixContactMin) (hCRS : RouteK.Selmer.CertifiedRankSel)
    (h22 : FixedPrimePattern) : FrozenTarget
```

## Statement corrections

None. One hypothesis is weaker than the task asked for:
- **The onto half needs only `d` odd.** It does not use `d ≡ 5 (mod 8)` or the squarefreeness of
  `d`. Lemma G1 (`loc_padic_good_iff`) needs only `p ∤ d`.

## Proofs

- **`prop0`.** It is p0-bits' `isSol_iff_selPair_mem_of_G2`, with Lemma G2 supplied as p0-good's
  `loc_padic_good_of_units`. The places ∞, 2 and `p ∣ d`, the primes `p ∤ 2d`
  (`not_dvd_selPair`) and the squarefreeness of `classInt` were already combined inside that lemma.
- **Onto half.**
  - For `(a, b) ∈ Sel2 d`, `loc_padic_good_iff` at each odd prime `p ∤ d` gives `p ∤ a` and `p ∤ b`.
  - Then `exists_classInt_eq` writes each of `a`, `b` as a `classInt` value:
    - if `a` is odd, it divides `d` (`dvd_of_squarefree_of_odd_primes_dvd`, via
      `Nat.prod_primeFactors_dvd_iff`), and `classInt_natClass` applies;
    - if `a = 2c`, then `c` is odd and squarefree, and `classInt d e₀ 1 w = 2 · classInt d e₀ 0 w`.
- **`certifiedRank_of_certifiedRankSel`** is `certifiedRank_of_sel hCRS prop0Statement`.
- **The Main variant** is `exists_bounded_integer_polynomial_defining_integers_of` applied to
  `certifiedRank_of_certifiedRankSel hCRS`. Its docstring gives CR₃^Sel in the literature's terms:
  for squarefree `d ≡ 5 (mod 8)`, `dim Sel₂(C_d) = 3` and a Selmer class with `|a| ≡ 7 (mod 8)`
  imply `Ш(C_d)[2] = 0`, equivalently `rank ≥ 1`. The sources are Kriz plus the corank lemma, or
  TYZ plus GZK. The existing theorems are unchanged.

## Lemmas added beyond the leaves (all in `ZInQ.RouteK.Selmer`, grepped against all branches)

- `classInt_one_eq_two_mul`
- `dvd_of_squarefree_of_odd_primes_dvd`
- `exists_classInt_eq`

## Problems

None. The worktree had no `.lake`, so I copied it from the main clone with `cp --reflink`.

## Suggestions for the next agent

- The lead can now state the main theorem's trust boundary as H, CR₃^Sel and 22P:
  - CR₃^Sel speaks only of `Sel₂(C_d)`;
  - Proposition 0 is a Lean theorem.

  The blueprint articles for nt-prop0 can point their `lean:` fields at the names above.
