---
article_id: af_09c5b3eb093213f55ba89e5b
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.PSide.cdEulerPoly_of_not_dvd, ZInQ.Contrib.PSide.cdCoeff_prime_pow_succ_succ, ZInQ.Contrib.PSide.LFunction_cd_prime_pow_succ_succ
---

# The recursion for the coefficients at a good prime

Let $d$ be a natural number, $p$ a prime with $p\nmid2d$, and $c_d(n)$ the numbers of
[the standard Euler product](l-series.md).

1. The [Euler polynomial](cd-euler-polynomial.md) of $C_d$ at $p$ is
   $P_{d,p}(T)=1-c_d(p)\,T+p\,T^2$.
2. For every $k\ge0$,
   $$c_d(p^{k+2})=c_d(p)\,c_d(p^{k+1})-p\,c_d(p^k).$$
3. If $d$ is odd and squarefree, then for every $k\ge0$
   $$a_{p^{k+2}}(C_d)=a_p(C_d)\,a_{p^{k+1}}(C_d)-p\,a_{p^k}(C_d),$$
   with $a_n(C_d)$ as in [the coefficients at prime powers](prime-power-coefficients.md).

**Proof sketch.** (1) By the definition of $P_{d,p}$ at $p\nmid2d$ and
[the coefficients for every $d$](coefficients-every-d.md) (4), $c_d(p)=p+1-N_d(p)$. (2) Let
$Q=P_{d,p}^{-1}$ with coefficients $q_j$; by the coefficients for every $d$ (3), $q_j=c_d(p^j)$.
By (1), the coefficient of $T^{k+2}$ in $P_{d,p}Q=1$ is
$q_{k+2}-c_d(p)\,q_{k+1}+p\,q_k=0$. (3) Rewrite each $a_n(C_d)$ as $c_d(n)$ by the coefficients
for every $d$ (7) and apply (2).

## Depends on

- [$L(C_d,s)$ is the Dirichlet series of the standard Euler product](l-series.md)
- [The Euler polynomial of $C_d$ at $p$](cd-euler-polynomial.md)
- [The coefficients of $L(C_d,s)$ at prime powers](prime-power-coefficients.md)

## Proof depends on

- [The coefficients $c_d(n)$ for every $d$](coefficients-every-d.md)

## Sources

- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
