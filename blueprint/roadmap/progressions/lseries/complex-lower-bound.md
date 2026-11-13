---
article_id: af_b9c9b6d9b611b2069c5cf24c
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Progressions.norm_LFunction_one_ge_of_sq_ne_one
---

# A lower bound for $|L(1,\chi)|$ at complex characters

Let $q\ge1$ and let $\chi$ be a Dirichlet character modulo $q$ with $\chi^2\ne\chi_0$ (so
$\chi$ takes a nonreal value). Put $M=\log q+3$. Then
$$|L(1,\chi)|\ge\frac1{256\,M^7}.$$

**Proof sketch.** For every real $x>0$ the Euler product gives the classical inequality
$$|L(1+x,\chi_0)|^3\,|L(1+x,\chi)|^4\,|L(1+x,\chi^2)|\ge1,$$
from $3+4\cos\theta+\cos2\theta\ge0$. Take $0<x\le1$. Then $|L(1+x,\chi_0)|\le1+1/x\le2/x$,
$|L(1+x,\chi^2)|\le M$ since $\chi^2$ is nonprincipal, and
$|L(1+x,\chi)|\le|L(1,\chi)|+xM^2$ by the variation bound. If $|L(1,\chi)|\le xM^2$, then
$|L(1+x,\chi)|\le2xM^2$ and
$1\le(8/x^3)(16x^4M^8)M=128\,xM^9$. With $x=1/(256M^9)\le1$ this is false, so
$|L(1,\chi)|>xM^2=1/(256M^7)$.

## Depends on

None.

## Proof depends on

- [A bound for $L(\sigma,\chi)$ near $1$](l-value-bound.md)
- [Variation of $L(\sigma,\chi)$ near $1$](l-value-variation.md)
- [The principal $L$-function to the right of $1$](trivial-character.md)

## Sources

- [Davenport, Chapter 4](../../../sources/progressions-locators.md#davenport-chapter-4)
