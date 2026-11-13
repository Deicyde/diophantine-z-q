---
article_id: af_1d209ee46eaeaa06074676e5
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Density.goodPrimeDensity
---

# Proposition D: the good slope primes have positive relative density

The good slope primes have positive relative upper density in the primes: there is $c>0$ such that
$\#(G\cap[0,N])\ge c\,\pi(N)$ for infinitely many $N$, where $G$ is the set of good slope primes.

This is the weak form of Proposition D, which the research note deduces from Theorem D through its
Proposition 5.3 ([Dirichlet density gives relative upper density](dirichlet-density.md)). It discharges
the density statement, the second input of the progressions of good slope primes.

**Proof sketch.** The uniform bad-prime bound holds, and Theorem D derives the density statement
from it.

## Depends on

- [The density statement for good slope primes](good-prime-density.md)

## Proof depends on

- [Theorem D: the density statement from the uniform bound](theorem-d.md)
- [The uniform bound holds](proposition-4-2.md)

## Sources

- [Assembly](../../sources/density-locators.md#assembly)
