# Lemma 5.4 from the Cassels–Tate square property (fork issue #83, follow-up to PR #90)

**Result (compiled, standard axioms), on top of PR #90 (`rc/thm53-headline-20261117` at `a04588b4`):**

* `PoleS12.lemma54At_of_casselsTate : PoleS12.CasselsTateSquareCurves → PoleRC.Lemma54At SelmerTwoPower.SelmerCorankOne`:
  the manuscript's Lemma 5.4 (`lem:corank`, lines 1072–1084) at the curves `E_ℓ`, from the Cassels–Tate square
  property of these curves (`SelmerTwoPower.CasselsTateSquare`: for every decomposition
  `Ш(E/ℚ)[2^∞] ≅ (ℚ₂/ℤ₂)^t × F` with `F` finite, `#F[2]` is a square).
* `PoleS12.lemma54_of_casselsTate : PoleRC.MordellWeil → (∀ E, E.IsElliptic → CasselsTateSquare E) → PoleS12.Lemma54`:
  the cited leaf `Lemma54` of PR #90 from Mordell–Weil and the Cassels–Tate square property for all curves.
* `PoleS12.poleCompleteness_of_restrictedConverseGenuine_casselsTate : RestrictedConverseGenuine →
  CasselsTateSquareCurves → BCDTThmA → KolyvaginThm1 → PoleCompleteness`: Theorem 5.2 by the proof of PR #90's
  `poleCompleteness_of_restrictedConverseGenuine_mw`, with `Lemma54At` from the Cassels–Tate property instead of
  from `Lemma54` and `KummerSelmerM`. With it, `frozenTarget`'s argument `h54 : PoleS12.Lemma54` can be replaced by
  `hCT : PoleS12.CasselsTateSquareCurves` (the receiving consumer, for the integrator).

Everything is over the Selmer groups of `SelmerTwoPower.lean` as main defines them (two families of completions,
`ℚ_p` and `ℝ`); no existing definition is changed.

## Files (all new)

* `CofinitePrimary.lean` (Mathlib only): a `p`-primary abelian group with finite `p`-torsion is
  `(ℚ_p/ℤ_p)^t × F` with `F` finite; counting lemmas.
* `SelmerFam.lean`: the same local fields indexed by `Nat.Primes ⊕ Unit` (one family, for Tau Ceti's descent
  sequences); `Fam.sha`, `Fam.selmerAt`, `Fam.selmerTwoPower`, `Fam.SelmerCorankOne`, and `Fam.sha_eq`,
  `Fam.selmerAt_eq`, `Fam.selmerTwoPower_eq`, `Fam.selmerCorankOne_iff`: they are the groups of `SelmerTwoPower`
  (reindexing only); `0 → E[2^n] → E[2^∞] → E[2^∞] → 0`; `Sel_{2^n} ↠ Sel_{2^∞}[2^n]`; existence of the corank.
* `SelmerCorankFam.lean`: Lemma 5.4 over the one-family groups
  (`Fam.selmerCorankOne_of_card_selmerAt_one`, from Mordell–Weil and the Cassels–Tate square property):
  `Sel_{2^∞}` is `2`-primary (continuous cocycles on the compact `G_ℚ` into a discrete module), the kernel of
  `Sel_{2^n} → Sel_{2^∞}` is bounded by `#E(ℚ)[2^∞]`, the `2^n`-descent sequences give
  `#Sel_{2^n} = #(E(ℚ)/2^n) · #Ш[2^n]`, and a growth comparison gives the corank.
* `Lemma54FromCasselsTate.lean`: `CasselsTateSquare` over `SelmerTwoPower.sha`, its equivalence with the
  one-family form, `CasselsTateSquareCurves`, and the three theorems above.

These are the proofs of the review branch `wip/selmer-descent-20261117` (commits `96b7f57f`, `ff6feee5`), moved
onto main's definitions without change of argument.
