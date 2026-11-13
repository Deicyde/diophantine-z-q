---
article_id: af_2f121851c83ac4b0c1680ec4
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Literature.LFunction_cd_apply_prime, ZInQ.Literature.LFunction_cd_apply_prime_of_dvd, ZInQ.Literature.natCard_point_shortCurve_zmod, ZInQ.Literature.LFunction_cd_apply_prime_eq_sub_card
---

# The coefficients of $L(C_d,s)$ at primes as point counts

With $a_n(C_d)$ the coefficients of $L(C_d,s)$ as in
[the coefficients at prime powers](prime-power-coefficients.md), and $p$ a prime:

1. If $d$ is odd and squarefree, then
   $$a_p(C_d)=\begin{cases}0 & \text{if } p\mid2d,\\ p+1-\#C_d(\mathbb F_p) & \text{if } p\nmid2d,\end{cases}$$
   where $\#C_d(\mathbb F_p)$ is the number of points of $y^2=x^3-d^2x$ over $\mathbb F_p$, the point
   at infinity included.
2. If $d$ is odd and squarefree and $p\mid2d$, then $a_p(C_d)=0$.
3. For every natural number $d$ with $p\nmid2d$,
   $$\#C_d(\mathbb F_p)=\#\{(x,y)\in\mathbb F_p^2:\ y^2=x^3-d^2x\}+1 .$$
4. If $d$ is odd and squarefree and $p\nmid2d$, then
   $$a_p(C_d)=p-\#\{(x,y)\in\mathbb F_p^2:\ y^2=x^3-d^2x\}.$$

The point-count formula (4) holds only at the primes $p\nmid2d$; at the primes $p\mid2d$ the
coefficient is $0$ by (2).

**Proof sketch.** (1) Take $k=1$ in [the coefficients at prime powers](prime-power-coefficients.md).
For a polynomial $P$ with $P(0)=1$, the coefficient of $T$ in $P^{-1}$ is minus the coefficient of
$T$ in $P$ (compare the coefficients of $T$ in $P\cdot P^{-1}=1$). The coefficient of $T$ in the
[Euler polynomial](cd-euler-polynomial.md) $P_{d,p}$ is $0$ if $p\mid2d$ and $-(p+1-\#C_d(\mathbb F_p))$
otherwise. (2) is the first case of (1). (3) Since $p\nmid2d$, both $2$ and $d$ are nonzero in
$\mathbb F_p$, so $-d^2\ne0$ and the discriminant $-64(-d^2)^3$ of $y^2=x^3-d^2x$ is nonzero;
by [point counts](point-counts.md) (3) the points are the affine solutions and the point at
infinity. (4) Combine (1) and (3).

## Depends on

- [The coefficients of $L(C_d,s)$ at prime powers](prime-power-coefficients.md)

## Proof depends on

- [The Euler polynomial of $C_d$ at $p$](cd-euler-polynomial.md)
- [Point counts under changes of variables and field isomorphisms](point-counts.md)

## Sources

- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
