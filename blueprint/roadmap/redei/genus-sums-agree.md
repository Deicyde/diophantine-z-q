---
article_id: af_8b9b8626f2736c4c06330576
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Redei.T5bCl_eq_T5b', ZInQ.RouteK.Rank5b.T5bCl_eq_T5b
---

# The genus sum of class numbers is the genus sum of Rédei bits

Let $d$ be odd and squarefree. Then
$$T^{\rm Cl}_{5b}(d)=T_{5b}(d):$$
the genus sum of row 5b with the genus class numbers $g(d_B)$ equals the genus sum with Rédei's
$g_d(B)$. Along the way, the same identity is proved for every odd squarefree $d$ from Rédei's
formula taken as an assumption.

**Proof sketch.** Both sums run over the same set partitions of the primes of $d$. Every block $B$
of such a partition is nonempty and has $d_B\equiv7$, $3$ or $1\pmod8$, so Rédei's formula, taken
as an assumption, gives $g(d_B)\equiv g_d(B)\pmod2$ factor by factor, and the two sums agree term
by term. By [Rédei's formula](redei-formula.md), its hypothesis holds, so
$T^{\rm Cl}_{5b}(d)=T_{5b}(d)$ for every odd squarefree $d$.

## Depends on

- [The genus sum of class numbers](class-number-genus-sum.md)
- [The genus sum $T_{5b}$](../rank-5b/genus-sum/genus-sum.md)
- [The statement of Rédei's formula](redei-formula-statement.md)

## Proof depends on

- [Rédei's formula](redei-formula.md)

## Sources

- [The hypothesis in class-number form](../../sources/redei-locators.md#the-hypothesis-in-class-number-form)
