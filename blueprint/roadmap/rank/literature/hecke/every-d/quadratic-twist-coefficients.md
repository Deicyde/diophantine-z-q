---
article_id: af_f262ae2708977dd12642578d
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeAll.jacobiSym_mul_right_all, ZInQ.Contrib.HeckeAll.jacobiSym_factorization, ZInQ.Contrib.HeckeAll.eulerCoeff, ZInQ.Contrib.HeckeAll.eulerCoeff_cast, ZInQ.Contrib.HeckeAll.eulerCoeff_zero, ZInQ.Contrib.HeckeAll.eulerCoeff_of_dvd, ZInQ.Contrib.HeckeAll.cdEulerPoly_twist, ZInQ.Contrib.HeckeAll.jacobiSym_sq_of_not_dvd, ZInQ.Contrib.HeckeAll.eulerCoeff_twist, ZInQ.Contrib.HeckeAll.cdCoeff_twist
---

# The coefficients of $C_d$ as a quadratic twist of $C_1$

For natural numbers $d,p,k$ let $e_{d,p}(k)$ be the coefficient of $T^k$ in $P_{d,p}(T)^{-1}$,
where $P_{d,p}$ is [the Euler polynomial](../../l-function-cd/cd-euler-polynomial.md); $c_d(n)$ are
the coefficients of [the standard Euler product](../../l-function-cd/l-series.md), and
$\left(\frac an\right)$ is the Jacobi symbol as in [the Hecke character](../gaussian/hecke-character.md).

1. For every integer $a$ and coprime natural numbers $x,y$,
   $\left(\frac a{xy}\right)=\left(\frac ax\right)\left(\frac ay\right)$; and for $n\ne0$,
   $\left(\frac an\right)=\prod_{p^k\parallel n}\left(\frac ap\right)^k$.
2. $e_{d,p}(0)=1$; reading $e_{d,p}(k)$ in $\mathbb C$ gives the coefficient of $T^k$ in the
   inverse of $P_{d,p}$ with complex coefficients; and if $p\mid2d$, then $e_{d,p}(k)=0$ for every
   $k\ge1$.
3. If $p$ is a prime with $p\nmid2d$, then there is an integer $b$ with
   $P_{d,p}=1-\left(\frac dp\right)bT+pT^2$ and $P_{1,p}=1-bT+pT^2$ (over $\mathbb C$), and
   $\left(\frac dp\right)^2=1$.
4. For every natural number $d$, prime $p$ and $k\ge0$,
   $e_{d,p}(k)=\left(\frac dp\right)^ke_{1,p}(k)$.
5. For every natural number $d$ and every $n\ge1$,
   $c_d(n)=\left(\frac dn\right)c_1(n)$.

**Proof sketch.** (1) Multiplicativity of the Jacobi symbol in its denominator (trivial when $x$
or $y$ is $0$, as coprimality then forces the other to be $1$), and induction over the
factorization.

(2) The constant coefficient of $P_{d,p}$ is $1$; reading coefficients in $\mathbb C$ commutes with
inversion ([quadratic power series](../gaussian/quadratic-power-series.md) (2)); for $p\mid2d$,
$P_{d,p}=1$.

(3) With $S=\sum_x\left(\frac{x^3-x}p\right)$: $p+1-N_e(p)=-\sum_x\left(\frac{x^3-e^2x}p\right)$
for $e=d$ and $e=1$ ([the coefficients at primes](../../l-function-cd/prime-coefficients.md) and
[the split primes from $y^2=x^3-x$](../deuring/gauss-split-twist.md) (1)), and the twist
$\sum_x\left(\frac{x^3-d^2x}p\right)=\left(\frac dp\right)S$ (the same article (2)); take $b=-S$.
$\left(\frac dp\right)=\pm1$ as $p\nmid d$.

(4) If $p\nmid2d$, by (3) and [quadratic power series](../gaussian/quadratic-power-series.md) (3)
with $\varepsilon=\left(\frac dp\right)$. If $p\mid2d$: the case $k=0$ is (2); for $k\ge1$ the
left side is $0$, and either $p\mid d$, so $\left(\frac dp\right)=0$, or $p=2$, so
$e_{1,2}(k)=0$ by (2).

(5) Both sides are products over $p^k\parallel n$: $c_d(n)=\prod e_{d,p}(k)$ by definition, and
$\left(\frac dn\right)=\prod\left(\frac dp\right)^k$ by (1); apply (4) factor by factor.

## Depends on

- [The Euler polynomial of $C_d$ at $p$](../../l-function-cd/cd-euler-polynomial.md)
- [$L(C_d,s)$ is the Dirichlet series of the standard Euler product](../../l-function-cd/l-series.md)
- [The Hecke character $\psi_d$](../gaussian/hecke-character.md)

## Proof depends on

- [Inverses of quadratic power series](../gaussian/quadratic-power-series.md)
- [The coefficients of $L(C_d,s)$ at primes as point counts](../../l-function-cd/prime-coefficients.md)
- [The split primes for $C_d$ from the curve $y^2=x^3-x$](../deuring/gauss-split-twist.md)

## Sources

- [The curves for even and non-squarefree d](../../../../../sources/hecke-locators.md#the-curves-for-even-and-non-squarefree-d)
