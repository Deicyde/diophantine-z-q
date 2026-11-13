---
article_id: af_57f9026e2107fde5a87ce794
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.PSide.card_solutions_eq, ZInQ.Contrib.PSide.charSum_odd_eq_zero, ZInQ.Contrib.PSide.LFunction_cd_apply_prime_eq_neg_charSum
---

# Point counts by the quadratic character

Let $F$ be a finite field with $q$ elements and $\chi$ its quadratic character: $\chi(0)=0$,
$\chi(c)=1$ for a nonzero square $c$ and $\chi(c)=-1$ for a non-square $c$.

1. If $F$ does not have characteristic $2$, then for every function $g:F\to F$
   $$\#\{(x,y)\in F^2:\ y^2=g(x)\}=q+\sum_{x\in F}\chi\bigl(g(x)\bigr).$$
2. If $\chi(-1)=-1$ and $g:F\to F$ is odd, that is $g(-x)=-g(x)$ for every $x$, then
   $\sum_{x\in F}\chi\bigl(g(x)\bigr)=0$.
3. If $d$ is odd and squarefree and $p$ is a prime with $p\nmid2d$, then, with $\chi$ the quadratic
   character of $\mathbb F_p$ and $a_p(C_d)$ as in
   [the coefficients at prime powers](prime-power-coefficients.md),
   $$a_p(C_d)=-\sum_{x\in\mathbb F_p}\chi\bigl(x^3-d^2x\bigr).$$

Over $\mathbb F_p$, for $g(x)=x^3+ax$, the same count with the point at infinity added is (1)
of [character sums for the curves $y^2=x^3+ax$](../../../density/character-sums.md).

**Proof sketch.** (1) In characteristic other than $2$, the equation $y^2=c$ has $1+\chi(c)$
solutions $y\in F$; sum over $x$ with $c=g(x)$. (2) The map $x\mapsto-x$ permutes $F$, so the sum
$S$ equals $\sum_x\chi\bigl(g(-x)\bigr)=\sum_x\chi(-1)\chi\bigl(g(x)\bigr)=-S$, and $S=0$.
(3) By [the coefficients at primes](prime-coefficients.md) (4),
$a_p(C_d)=p-\#\{(x,y)\in\mathbb F_p^2:\ y^2=x^3-d^2x\}$. Since $p\nmid2d$, $p\ne2$, so
$\mathbb F_p$ does not have characteristic $2$; (1) with $g(x)=x^3-d^2x$ and $q=p$ gives the
claim.

## Depends on

- [The coefficients of $L(C_d,s)$ at prime powers](prime-power-coefficients.md)

## Proof depends on

- [The coefficients of $L(C_d,s)$ at primes as point counts](prime-coefficients.md)

## Sources

- [Character sums](../../../../sources/density-locators.md#character-sums)
- [The Hasse bound for the congruent number curves](../../../../sources/rank-locators.md#the-hasse-bound-for-the-congruent-number-curves)
- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
