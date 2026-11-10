---
article_id: af_671b769c2e6f8cc663634a5a
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.Density.UniformBadBound
---

# The uniform bound for the primes bad at a medium $\ell$

The *uniform bad-prime bound* is the assertion that there are constants $A>0$ and $N_1$ such that for
every $N\ge N_1$ and every prime $\ell\equiv1\pmod4$ with $5\le\ell$ and $\ell^4\le N$,
$$\#\bigl(\mathrm{Bad}_\ell\cap[0,N]\bigr)\le\frac{A\,N}{\ell^2\log N}.$$

It is Proposition 4.2 of the research note, isolated as a statement so that Theorem D can be proved
from it before the sieve; it is proved in [the uniform bound holds](proposition-4-2.md).

## Depends on

- [A subset of good slope primes](good-subset.md)

## Sources

- [The sieve](../../sources/density-locators.md#the-sieve)
