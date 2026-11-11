---
article_id: af_2bf8076bd166679a24683be2
declaration: def
origin: cited
statement: formalized
lean: ZInQ.RouteK.Rank5b.RedeiFormula
---

# The statement of Rédei's formula

*Rédei's formula* is the following assertion. Let $d$ be odd and squarefree, and let $B$ be a
nonempty set of primes of $d$ whose product $d_B=\prod_{p\in B}p$ satisfies
$d_B\equiv7$, $3$ or $1\pmod8$. Then
$$g(d_B)\equiv g_d(B)\pmod 2,$$
where $g(d_B)$ is the genus class number of $d_B$, the order of the subgroup of squares of the
class group of $\mathbb Q(\sqrt{-d_B})$, and $g_d(B)\in\mathbb F_2$ is Rédei's $g$ of $B$ for the
bits $a_{pq}$, $y_p$, $z_p$ of the primes of $d$:
$$g_d(B)=\sum_{\rho\in B}y_\rho\,\kappa_\rho(B)\ \text{ if }y(B)=1,\qquad
g_d(B)=\sum_{\rho\in B}z_\rho\,\kappa_\rho(B)\ \text{ if }y(B)=0.$$

The blocks allowed include every block that occurs in the genus sum $T_{5b}(d)$: the blocks of a set
partition are nonempty, and the partitions counted by the genus sum have only blocks with
$d_B\equiv7$, $3$ or $1\pmod8$. Blocks with $d_B\equiv5\pmod8$ never occur. The empty set is
excluded because $g(1)=1$ (the class group of $\mathbb Q(i)$ is classically trivial), while Rédei's
$g$ of the empty set is $0$.

## Depends on

- [The genus class number](genus-class-number.md)
- [Rédei's $g$ from the bits](../rank-5b/genus-sum/redei-g.md)
- [The genus sum $T_{5b}$](../rank-5b/genus-sum/genus-sum.md)

## Sources

- [The target](../../sources/redei-locators.md#the-target)
- [Rédei's formulas](../../sources/redei-locators.md#redeis-formulas)
- [Rédei 1934](../../sources/redei-locators.md#redei-1934)
