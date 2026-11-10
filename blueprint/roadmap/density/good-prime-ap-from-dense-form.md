---
article_id: af_46b86f5024883219cc620317
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Density.goodPrimeAP_of_greenTaoDense', ZInQ.Density.goodPrimeAP_of_greenTaoDense_uniformBadBound
---

# Progressions of good slope primes from Szemerédi's theorem in the primes alone

Assume Szemerédi's theorem in the primes (every set of primes of positive relative upper density
contains arithmetic progressions of every finite length). Then the statement 22P_AP holds: for every
$K$ there are $x\ge1$ and $v\ge1$ such that the $K+1$ numbers $x+jv$ ($0\le j\le K$) are good slope
primes larger than every prime of $S_b$.

Since Szemerédi's theorem in the primes is itself proved, this is an intermediate form; the same
conclusion follows from Szemerédi's theorem in the primes and the uniform bad-prime bound.

**Proof sketch.** Proposition D gives the density statement, and the two together give 22P_AP.

## Depends on

- [Szemerédi's theorem in the primes](../green-tao/dense-form.md)
- [The statement 22P_AP](../route-ap/good-prime-ap.md)

## Proof depends on

- [Proposition D: the good slope primes have positive relative density](proposition-d.md)
- [22P_AP from Szemerédi's theorem in the primes and the density statement](../route-ap/good-prime-ap-from-green-tao.md)

## Sources

- [Assembly](../../sources/density-locators.md#assembly)
