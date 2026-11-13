---
article_id: af_8485116fcdbc8ca1a16ac14f
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.PSide.cdLocalSeries, ZInQ.Contrib.PSide.cdCoeff_zero, ZInQ.Contrib.PSide.cdCoeff_one, ZInQ.Contrib.PSide.cdArith, ZInQ.Contrib.PSide.cdCoeff_mul, ZInQ.Contrib.PSide.isMultiplicative_cdArith, ZInQ.Contrib.PSide.cdCoeff_prime_pow, ZInQ.Contrib.PSide.cdCoeff_prime, ZInQ.Contrib.PSide.cdCoeff_prime_pow_of_dvd, ZInQ.Contrib.PSide.cdCoeff_eq_zero_of_dvd, ZInQ.Contrib.PSide.cdCoeff_eq_zero_of_even, ZInQ.Contrib.PSide.LFunction_cd_eq_cdCoeff
---

# The coefficients $c_d(n)$ for every $d$

Let $d$ be a natural number and $c_d(n)$ the numbers of
[the standard Euler product](l-series.md). For a prime $p$ let $Q_{d,p}(T)=P_{d,p}(T)^{-1}$ be the
inverse, as a power series with integer coefficients, of the
[Euler polynomial](cd-euler-polynomial.md) $P_{d,p}$ (its constant coefficient is $1$). Unlike the
identification with $L(C_d,s)$, items (1) to (6) hold for every $d$, even or not squarefree.

1. $c_d(0)=0$ and $c_d(1)=1$; so $n\mapsto c_d(n)$ is an arithmetic function.
2. $c_d(mn)=c_d(m)\,c_d(n)$ for coprime natural numbers $m$ and $n$; so $c_d$ is a multiplicative
   arithmetic function.
3. For a prime $p$ and $k\ge0$, $c_d(p^k)$ is the coefficient of $T^k$ in $Q_{d,p}(T)$.
4. For a prime $p$,
   $$c_d(p)=\begin{cases}0 & \text{if } p\mid2d,\\ p+1-N_d(p) & \text{if } p\nmid2d,\end{cases}$$
   with $N_d(p)$ the number of points of the [model $y^2=x^3-d^2x$](cd-model.md) over
   $\mathbb Z/p\mathbb Z$, the point at infinity included.
5. If $p$ is a prime with $p\mid2d$ and $k\ge1$, then $c_d(p^k)=0$.
6. If a prime $p$ with $p\mid2d$ divides $n$, then $c_d(n)=0$. In particular $c_d(n)=0$ for every
   even $n$.
7. If $d$ is odd and squarefree, then $a_n(C_d)=c_d(n)$ for every $n$ (both are $0$ at $n=0$), with
   $a_n(C_d)$ as in [the coefficients at prime powers](prime-power-coefficients.md).

**Proof sketch.** (1) By definition, $c_d(1)$ being the empty product. (2) If $m=0$, coprimality
forces $n=1$, and both sides are $0$; likewise if $n=0$. Otherwise the prime powers exactly
dividing $mn$ are those of $m$ together with those of $n$, over disjoint sets of primes, so the
product defining $c_d(mn)$ splits. (3) The only prime dividing $p^k$ is $p$, with exponent $k$;
for $k=0$ both sides are $1$. (4) Take $k=1$ in (3): the coefficient of $T$ in $Q_{d,p}$ is minus
the coefficient of $T$ in $P_{d,p}$ (compare the coefficients of $T$ in $P_{d,p}Q_{d,p}=1$), which
is $0$ if $p\mid2d$ and $-(p+1-N_d(p))$ otherwise. (5) For $p\mid2d$, $P_{d,p}=1$, so
$Q_{d,p}=1$, whose coefficient of $T^k$ is $0$ for $k\ge1$; apply (3). (6) If $n=0$ use (1).
Otherwise write $n=p^km$ with $p\nmid m$; $k\ge1$ since $p\mid n$. By (2) and (5),
$c_d(n)=c_d(p^k)c_d(m)=0$. For even $n$ take $p=2$, which divides $2d$. (7) For $n\ne0$ both sides
are the same product, by [every coefficient](coefficients.md) (2); at $n=0$ both are $0$.

## Depends on

- [$L(C_d,s)$ is the Dirichlet series of the standard Euler product](l-series.md)
- [The Euler polynomial of $C_d$ at $p$](cd-euler-polynomial.md)
- [The model $y^2=x^3-d^2x$ over a ring](cd-model.md)
- [The coefficients of $L(C_d,s)$ at prime powers](prime-power-coefficients.md)

## Proof depends on

- [Every coefficient of $L(C_d,s)$](coefficients.md)

## Sources

- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
