---
article_id: af_1193d25d896b045fb266ea4f
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.redeiB_primeFactors, ZInQ.RouteK.Redei.redeiB_prime, ZInQ.RouteK.Redei.redeiB_ne_two, ZInQ.RouteK.Redei.redeiB_mem_primeFactors, ZInQ.RouteK.Redei.redeiB_mem_primeFactors_iff, ZInQ.RouteK.Redei.redeiB_two_not_mem, ZInQ.RouteK.Redei.redeiB_odd, ZInQ.RouteK.Redei.redeiB_squarefree, ZInQ.RouteK.Redei.redeiB_mem_ramSet, ZInQ.RouteK.Redei.redeiB_two_mem_ramSet_iff, ZInQ.RouteK.Redei.redeiB_mem_ramSet_cases, ZInQ.RouteK.Redei.redeiB_mod4_iff, ZInQ.RouteK.Redei.redeiB_one_lt, ZInQ.RouteK.Redei.redeiB_div_eq
---

# The primes of $d_B$

Let $d$ be a natural number, $B$ a set of primes of $d$ and $d_B=\prod_{p\in B}p$. Then:

- the primes of $d_B$ are exactly the elements of $B$, and $d_B$ is squarefree;
- if $B$ is nonempty, then $d_B>1$;
- for $q\in B$, $d_B/q=\prod_{k\in B,\,k\ne q}k$;
- every element of $B$ lies in $T_{d_B}$, and every element of $T_{d_B}$ is $2$ or an element of $B$.

If $d$ is odd, then moreover:

- the primes of $d$ are different from $2$, so $2$ is not a prime of $d_B$ and $d_B$ is odd;
- $2\in T_{d_B}$ if and only if $d_B\not\equiv3\pmod4$;
- $y(B)=\sum_{q\in B}y_q=1$ if and only if $d_B\equiv3\pmod4$.

**Proof sketch.** $d_B$ is a product of distinct primes, so its primes are the elements of $B$ and
it is squarefree; the statements about $T_{d_B}$ follow from its definition. For odd $d$, $y(B)$ is
$\lambda(d_B)=[d_B\equiv3\pmod4]$, by the multiplicativity of $\lambda$ on odd residues modulo $8$.

## Depends on

- [The genus sum $T_{5b}$](../../rank-5b/genus-sum/genus-sum.md)
- [The ramified primes and the ideals $\mathfrak p_p$](../field/ramified-primes.md)
- [Smith's matrices $L$, $M_1$ and $M_{5b}$](../../rank-5b/smith-matrices.md)

## Proof depends on

- [The genus sum of an odd number from its bits](../../rank-5b/genus-sum/genus-sum-bits.md)

## Sources

- [Step 8: the bridge](../../../sources/redei-locators.md#step-8-the-bridge)
