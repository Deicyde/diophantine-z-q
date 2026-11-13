---
article_id: af_b9a22f7edc26632919f81c4e
declaration: structure
origin: bridged
statement: formalized
lean: ZInQ.Mult.GoodSlopeAP, ZInQ.Mult.OldBounds
---

# Slopes with poles at the old primes: field 2′

For a real $B_0$, say that $t\in\mathbb Q$ satisfies *conditions 1, 2′, 3, 4 for $B_0$* if it
satisfies conditions 1, 3 and 4 of the slope representation for $B_0$ and, in place of
condition 2:

- **2′.** for every $p\in S_b$, either the bounds of condition 2 hold at $p$,
  $$|v_p(t-1)|\le B_p\quad\text{and}\quad|v_p(F(t)/(t-1)^8)|\le8B_p,$$
  or $F(t)>0$ and $t$ satisfies the hypotheses of Lemma P at $p$.

Every $t$ satisfying conditions 1–4 for $B_0$ satisfies conditions 1, 2′, 3, 4 for $B_0$.

Field 2′ allows a pole of any order at an old prime, provided the seven numerators $u-cv$,
$c\in\mathcal C\cup\{1\}$, are prime to it; this is what a progression of primes provides, whose
common difference is divisible by every small prime to a high power.

## Depends on

- [The slope representation](../multiplication/completeness/slope-representation.md)
- [The hypotheses of Lemma P](pole-absorption-hypotheses.md)

## Sources

- [The modified completeness argument](../../sources/route-ap-locators.md#the-modified-completeness-argument)
