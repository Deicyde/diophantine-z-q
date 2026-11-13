---
article_id: af_ff49080ebb824f9a3de82ab5
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.HeckePrimePowSplit, ZInQ.Contrib.HeckeFE.heckePrimePowSplit, ZInQ.Contrib.HeckeFE.HeckePrimePow, ZInQ.Contrib.HeckeFE.heckePrimePow_of_split
---

# The Hecke relation at prime powers

Let $d$ be a natural number and $\lambda_d$ the [Hecke coefficients](hecke-coefficients.md).

- The *Hecke relation at the split primes* holds for $d$ if for every prime $p\equiv1\pmod4$ with
  $p\nmid d$ and every $k\ge0$,
  $$\lambda_d(p^{k+2})=\lambda_d(p)\lambda_d(p^{k+1})-p\,\lambda_d(p^k).$$
- The *Hecke relation at all primes* holds for $d$ if for every prime $p$ and every $k\ge0$,
  $$\lambda_d(p^{k+2})=\lambda_d(p)\lambda_d(p^{k+1})-b_p\,\lambda_d(p^k),\qquad
  b_p=\begin{cases}0&p\mid2d,\\p&p\nmid2d.\end{cases}$$

1. The Hecke relation at the split primes holds for every natural number $d$.
2. If $d$ is odd and squarefree and the Hecke relation at the split primes holds for $d$, then the
   Hecke relation at all primes holds for $d$.

**Proof sketch.** (1) Let $p\equiv1\pmod4$, $p\nmid d$. Write $p=a^2+b^2$ (Fermat) and
$\pi=a+bi$. By [the Gaussian primes above a split prime](norm-fibres-split.md) (g) and the invariance of $\psi_d$
under units ([Hecke character](hecke-character.md) (3)),
$\sum_{A_p}\psi_d=4\psi_d(\pi)+4\psi_d(\bar\pi)$. By multiplicativity of $\psi_d$ and norm fibres at
primes (4), $\psi_d(\pi)\sum_{A_{p^{k+1}}}\psi_d$ is the sum of $\psi_d$ over the elements of
$A_{p^{k+2}}$ divisible by $\pi$, and likewise for $\bar\pi$. Every element of $A_{p^{k+2}}$ is
divisible by $\pi$ or $\bar\pi$, by both exactly when it is divisible by $p$ (the Gaussian primes above a split prime
(f)), and the elements divisible by $p$ are $p\delta$, $\delta\in A_{p^k}$ (norm fibres at primes
(4) with $z=p$, of norm $p^2$), with $\psi_d(p\delta)=p\,\psi_d(\delta)$ (Hecke character (4)). Inclusion–exclusion
gives
$$\Bigl(\sum_{A_p}\psi_d\Bigr)\Bigl(\sum_{A_{p^{k+1}}}\psi_d\Bigr)
=4\Bigl(\sum_{A_{p^{k+2}}}\psi_d+p\sum_{A_{p^k}}\psi_d\Bigr),$$
and dividing by $16$ gives the relation.

(2) Let $p$ be prime. If $p\mid2d$, then $\lambda_d(p)=0$ and $\lambda_d(p^{k+2})=0$
([non-split primes](hecke-coefficients-non-split.md) (3), and (1) for $p=2$ or (2) for $p\mid d$),
so both sides vanish. If $p\nmid2d$ and $p\equiv1\pmod4$, this is the hypothesis. If $p\equiv3\pmod4$,
then $\lambda_d(p)=0$ because $A_p$ is empty ([norm fibres at primes](norm-fibres-primes.md) (1)),
and non-split primes (4) gives the relation.

## Depends on

- [The coefficients of the Hecke L-series $L(\psi_d,s)$](hecke-coefficients.md)

## Proof depends on

- [Gaussian integers whose norm is a prime power](norm-fibres-primes.md)
- [The Gaussian primes above a split prime](norm-fibres-split.md)
- [The Hecke character $\psi_d$](hecke-character.md)
- [The Hecke coefficients at the primes that do not split](hecke-coefficients-non-split.md)

## Sources

- [Deuring and the Hecke character](../../../../../sources/hecke-locators.md#deuring-and-the-hecke-character)
- [Arithmetic of the Gaussian integers](../../../../../sources/hecke-locators.md#arithmetic-of-the-gaussian-integers)
