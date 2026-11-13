---
article_id: af_a96803d9ba74b2e716af66cc
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.Literature.Admissible5aNat, ZInQ.Literature.T5aCl
---

# The first genus sum $T^{\rm Cl}_{5a}$

Let $d$ be a natural number. For a set $B$ of primes of $d$ write $d_B=\prod_{p\in B}p$. A set
partition $\pi$ of the primes of $d$ is *admissible for row 5a* if exactly one block $B$ of $\pi$
has $d_B\equiv5\pmod8$ and every block $B$ of $\pi$ has $d_B\equiv5$ or $d_B\equiv1\pmod8$. The
*first genus sum of class numbers* is
$$T^{\rm Cl}_{5a}(d)=\sum_{\pi}\prod_{B\in\pi}g(d_B)\pmod 2,$$
the sum over the set partitions $\pi$ of the primes of $d$ that are admissible for row 5a, where
$g$ is the genus class number.

This is the set-partition form of Tian–Yuan–Zhang's first sum for $n\equiv5\pmod8$, including the
one-block partition. No identity with their printed sum is proved here.

## Depends on

- [The genus class number](../../redei/genus-class-number.md)
- [The genus sum of class numbers](../../redei/class-number-genus-sum.md)

## Sources

- [Reading A of Tian-Yuan-Zhang](../../../sources/rank-locators.md#reading-a-of-tian-yuan-zhang)
