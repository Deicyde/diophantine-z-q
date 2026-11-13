---
article_id: af_933d8aa9fa848334c1d63c21
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.PSide.recurrence_bound, ZInQ.Contrib.PSide.cdCoeff_prime_pow_sq_le, ZInQ.Contrib.PSide.cdCoeff_sq_le
---

# Bounds for the coefficients $c_d(n)$

Let $c_d(n)$ be the numbers of [the standard Euler product](l-series.md), and $\sigma_0(n)$ the
number of divisors of $n$, with $\sigma_0(0)=0$.

1. Let $a$ and $r\ge0$ be real numbers with $a^2\le4r^2$, and $(u_k)_{k\ge0}$ real numbers with
   $u_0=1$, $u_1=a$ and $u_{k+2}=a\,u_{k+1}-r^2u_k$ for every $k$. Then $|u_k|\le(k+1)\,r^k$ for
   every $k$.
2. For every natural number $d$, every prime $p$ and every $k\ge0$,
   $c_d(p^k)^2\le(k+1)^2p^k$.
3. For every natural numbers $d$ and $n$, $c_d(n)^2\le\sigma_0(n)^2\,n$, that is
   $|c_d(n)|\le\sigma_0(n)\sqrt n$.

**Proof sketch.** (1) Put $\delta=\sqrt{4r^2-a^2}$ and $\alpha,\beta=(a\pm i\delta)/2$, so that
$\alpha+\beta=a$, $\alpha\beta=r^2$ and $|\alpha|=|\beta|=r$. Let
$s_k=\sum_{i=0}^k\alpha^i\beta^{k-i}$; then $s_0=1$ and $s_{k+1}=\alpha^{k+1}+\beta s_k$. From this,
$s_1=a$ and $s_{k+2}=a\,s_{k+1}-r^2s_k$, so $u_k=s_k$ for every $k$ by induction. By induction,
$|s_{k+1}|\le r^{k+1}+r\,(k+1)r^k=(k+2)\,r^{k+1}$. (2) If $p\mid2d$: for $k=0$ both sides are $1$,
and for $k\ge1$, $c_d(p^k)=0$ by [the coefficients for every $d$](coefficients-every-d.md) (5).
If $p\nmid2d$, apply (1) with $a=c_d(p)$, $r=\sqrt p$ and $u_k=c_d(p^k)$: $u_0=c_d(1)=1$ (the
coefficients for every $d$ (1)), $a^2\le4p=4r^2$ by [Hasse's bound for $C_d$](hasse-bound.md) (2),
and the recursion is [the recursion at a good prime](good-prime-recursion.md) (2). Square the
bound $|c_d(p^k)|\le(k+1)\sqrt p^{\,k}$. (3) Induct over the factorization of $n$. For $n=0$ both
sides are $0$, and for $n=1$ both are $1$. For $n=p^k$ with $k\ge1$, $\sigma_0(p^k)=k+1$ and (2)
applies. For coprime $m,n$ the bound for $mn$ is the product of the bounds for $m$ and for $n$,
since $c_d$ ([the coefficients for every $d$](coefficients-every-d.md) (2)) and $\sigma_0$ are
multiplicative.

## Depends on

- [$L(C_d,s)$ is the Dirichlet series of the standard Euler product](l-series.md)

## Proof depends on

- [The coefficients $c_d(n)$ for every $d$](coefficients-every-d.md)
- [Hasse's bound for $C_d$](hasse-bound.md)
- [The recursion for the coefficients at a good prime](good-prime-recursion.md)

## Sources

- [The Hasse bound for the congruent number curves](../../../../sources/rank-locators.md#the-hasse-bound-for-the-congruent-number-curves)
