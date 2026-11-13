---
article_id: af_51d3ee8cf19d3d745f463808
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.PSide.quadraticChar_zmod_neg_one_of_mod_four, ZInQ.Contrib.PSide.natCard_point_cd_of_mod_four_eq_three, ZInQ.Contrib.PSide.LFunction_cd_apply_prime_of_mod_four_eq_three, ZInQ.Contrib.PSide.LFunction_cd_apply_prime_of_mod_four_eq_three', ZInQ.Contrib.PSide.cdCoeff_prime_of_mod_four_eq_three, ZInQ.Contrib.PSide.cdCoeff_prime_pow_of_mod_four_eq_three, ZInQ.Contrib.PSide.LFunction_cd_prime_pow_of_mod_four_eq_three
---

# The coefficients of $L(C_d,s)$ at the primes $p\equiv3\pmod4$

Let $p$ be a prime with $p\equiv3\pmod4$, $\chi$ the quadratic character of $\mathbb F_p$,
$c_d(n)$ the numbers of [the standard Euler product](l-series.md), and $a_n(C_d)$ the coefficients
of $L(C_d,s)$ as in [the coefficients at prime powers](prime-power-coefficients.md).

1. $\chi(-1)=-1$.
2. For every natural number $d$ with $p\nmid2d$, $\#C_d(\mathbb F_p)=p+1$, where
   $\#C_d(\mathbb F_p)$ is the number of points of $y^2=x^3-d^2x$ over $\mathbb F_p$, the point at
   infinity included.
3. If $d$ is odd and squarefree and $p\nmid2d$, then $a_p(C_d)=0$.
4. If $d$ is odd and squarefree and $p\nmid d$, then $a_p(C_d)=0$.
5. For every natural number $d$ with $p\nmid2d$: $c_d(p)=0$, and for every $k\ge0$
   $$c_d(p^{2k})=(-p)^k,\qquad c_d(p^{2k+1})=0 .$$
6. If $d$ is odd and squarefree and $p\nmid2d$, then for every $k\ge0$
   $$a_{p^{2k}}(C_d)=(-p)^k,\qquad a_{p^{2k+1}}(C_d)=0 .$$

By [the recursion at a good prime](good-prime-recursion.md) (1) and $c_d(p)=0$, the Euler
polynomial at $p$ is $1+pT^2$.

**Proof sketch.** (1) Since $p\ne2$, $\chi(-1)=\chi_4(p)$, where $\chi_4$ is the nontrivial character
modulo $4$ (the first supplement to quadratic reciprocity), and $\chi_4(p)=-1$ for
$p\equiv3\pmod4$. (2) Since $p\nmid2d$, the points are the solutions
in $\mathbb F_p^2$ and the point at infinity ([the coefficients at primes](prime-coefficients.md)
(3)). As $p\ne2$, [point counts by the quadratic character](quadratic-character-counts.md) (1)
counts the solutions as $p+\sum_x\chi(x^3-d^2x)$; the function $x\mapsto x^3-d^2x$ is odd, so by
(1) and point counts by the quadratic character (2) the sum is $0$. (3) Point counts by the
quadratic character (3) writes $a_p(C_d)$ as minus the same sum, which is $0$ as in (2). (4) A
prime dividing $2$ is $2$, which is not $3$ modulo $4$; so $p\nmid2$, and with $p\nmid d$ this gives
$p\nmid2d$; apply (3). (5) By [Hasse's bound for $C_d$](hasse-bound.md) (1),
$c_d(p)=-\varphi(-d^2)=-\sum_x\chi(x^3-d^2x)$, which is $0$ as in (2). Induct on $k$: for $k=0$,
$c_d(1)=1$ and $c_d(p)=0$ ([the coefficients for every $d$](coefficients-every-d.md) (1)). By
[the recursion at a good prime](good-prime-recursion.md) (2) and $c_d(p)=0$,
$c_d(p^{2k+2})=-p\,c_d(p^{2k})=(-p)^{k+1}$ and $c_d(p^{2k+3})=-p\,c_d(p^{2k+1})=0$. (6) By the
coefficients for every $d$ (7), $a_n(C_d)=c_d(n)$; apply (5).

## Depends on

- [$L(C_d,s)$ is the Dirichlet series of the standard Euler product](l-series.md)
- [The coefficients of $L(C_d,s)$ at prime powers](prime-power-coefficients.md)

## Proof depends on

- [The coefficients of $L(C_d,s)$ at primes as point counts](prime-coefficients.md)
- [Point counts by the quadratic character](quadratic-character-counts.md)
- [Hasse's bound for $C_d$](hasse-bound.md)
- [The coefficients $c_d(n)$ for every $d$](coefficients-every-d.md)
- [The recursion for the coefficients at a good prime](good-prime-recursion.md)

## Sources

- [The coefficients of the congruent number curves at the primes 3 mod 4](../../../../sources/rank-locators.md#the-coefficients-of-the-congruent-number-curves-at-the-primes-3-mod-4)
- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
