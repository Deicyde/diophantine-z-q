---
article_id: af_1321f1f06a91780dddd8a9f2
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.GoodPrimeAP
---

# The statement 22P_AP: long progressions of good slope primes

The statement 22P_AP is the assertion that for every $K\in\mathbb N$ there are integers $x\ge1$
and $v\ge1$ such that each of the $K+1$ numbers
$$x,\ x+v,\ x+2v,\ \dots,\ x+Kv$$
is a good slope prime larger than every prime of $S_b=S_{\rm ht}\cup\mathcal H$.

It mentions neither an integer to be represented, nor the catalogue multipliers, nor valuations
at the old primes, except through the lower bound $\max S_b$; and it places no condition on the
common difference $v$. It replaces the twenty-two-prime pattern as the arithmetic input of the
completeness of the multiplication template. It was introduced as a hypothesis and is now proved:
it follows from Szemerédi's theorem in the primes and the positive density of the good slope
primes ([22P_AP from Green–Tao and Proposition D](good-prime-ap-from-green-tao.md)), both proved
here.

## Depends on

- [The two-slope prime pattern](../main/two-slope-pattern.md)
- [Prime sets and clearing exponents of the multiplication certificate](../multiplication/certificate/constants.md)

## Sources

- [The progression form](../../sources/route-ap-locators.md#the-progression-form)
