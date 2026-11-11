---
article_id: af_450b0d71d54939e58a8ff955
declaration: def
origin: cited
statement: formalized
lean: ZInQ.RouteK.Rank5b.T5bCl, ZInQ.RouteK.Rank5b.neZero_dProd
---

# The genus sum of class numbers

For a natural number $d$ and a set $B$ of primes of $d$, the product $d_B=\prod_{p\in B}p$ is a
positive integer, so its genus class number $g(d_B)$ is defined. The *genus sum of class numbers*
of row 5b is
$$T^{\rm Cl}_{5b}(d)=\sum_{\pi}\prod_{B\in\pi}g(d_B)\pmod 2,$$
the sum over the set partitions $\pi$ of the primes of $d$ with exactly one block $B$ having
$d_B\equiv7\pmod8$, exactly one having $d_B\equiv3\pmod8$, and every block having
$d_B\equiv7$, $3$ or $1\pmod8$. These are the set partitions of the genus sum $T_{5b}(d)$; the
sum $T^{\rm Cl}_{5b}(d)$ has Tian, Yuan and Zhang's genus class numbers $g(d_B)$ in place of
Rédei's $g_d(B)$.

## Depends on

- [The genus class number](genus-class-number.md)
- [The genus sum $T_{5b}$](../rank-5b/genus-sum/genus-sum.md)

## Sources

- [The hypothesis in class-number form](../../sources/redei-locators.md#the-hypothesis-in-class-number-form)
- [Tian-Yuan-Zhang](../../sources/redei-locators.md#tian-yuan-zhang)
