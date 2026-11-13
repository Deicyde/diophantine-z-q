---
article_id: af_69e89971700102d149656674
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.heckeEulerPoly, ZInQ.Contrib.HeckeFE.HeckeEuler, ZInQ.Contrib.HeckeFE.heckeEuler_of_mult_primePow, ZInQ.Contrib.HeckeFE.heckeEuler_of_odd
---

# The Euler product of $L(\psi_d,s)$

For natural numbers $d$ and $p$, the *Hecke Euler polynomial* is the complex polynomial
$$H_{d,p}(T)=\begin{cases}1&p\mid2d,\\1-\lambda_d(p)T+pT^2&p\nmid2d,\end{cases}$$
with $\lambda_d$ the [Hecke coefficients](hecke-coefficients.md). The Hecke coefficients have the
*Euler product* for $d$ if for every $n\ge1$
$$\lambda_d(n)=\prod_{p^k\parallel n}[T^k]\,H_{d,p}(T)^{-1}.$$

1. If $d$ is odd and squarefree, the Hecke coefficients are
   [multiplicative](hecke-multiplicative.md) and the
   [Hecke relation at all primes](hecke-split-recursion.md) holds for $d$, then the Euler product
   holds for $d$.
2. If $d$ is odd and squarefree, the Euler product holds for $d$.

**Proof sketch.** (1) Multiplicativity and $\lambda_d(1)=1$ write $\lambda_d(n)$ as the product of
$\lambda_d(p^k)$ over $p^k\parallel n$, so it suffices to show
$\lambda_d(p^k)=[T^k]H_{d,p}(T)^{-1}$. Put $b_p=0$ for $p\mid2d$ and $b_p=p$ otherwise. Then
$H_{d,p}=1-\lambda_d(p)T+b_pT^2$ in both cases, since $\lambda_d(p)=0$ for $p\mid2d$
([non-split primes](hecke-coefficients-non-split.md) (3)). The coefficients of
$(1-\lambda_d(p)T+b_pT^2)^{-1}$ satisfy $\psi_0=1$, $\psi_1=\lambda_d(p)$ and
$\psi_{k+2}=\lambda_d(p)\psi_{k+1}-b_p\psi_k$ ([quadratic power series](quadratic-power-series.md)
(1)), as do $\lambda_d(p^k)$ by the Hecke relation; induction on $k$.

(2) By (1): the Hecke coefficients are multiplicative for every $d$, the Hecke relation at the split
primes holds for every $d$, and for odd squarefree $d$ it extends to all primes
([the Hecke relation](hecke-split-recursion.md) (1), (2)).

## Depends on

- [The coefficients of the Hecke L-series $L(\psi_d,s)$](hecke-coefficients.md)
- [The Hecke coefficients are multiplicative](hecke-multiplicative.md)
- [The Hecke relation at prime powers](hecke-split-recursion.md)

## Proof depends on

- [The Hecke coefficients at the primes that do not split](hecke-coefficients-non-split.md)
- [Inverses of quadratic power series](quadratic-power-series.md)

## Sources

- [Deuring and the Hecke character](../../../../../sources/hecke-locators.md#deuring-and-the-hecke-character)
