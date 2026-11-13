---
article_id: af_1cf1c055d5f15c3611c7e72a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.GaussFE.psiPair, ZInQ.Contrib.GaussFE.psiPair_neg, ZInQ.Contrib.GaussFE.psiPair_conj, ZInQ.Contrib.GaussFE.psiPair_primary, ZInQ.Contrib.GaussFE.gaussPointCount
---

# Gauss's point count holds

For a Gaussian integer $\alpha$ let $P(\alpha)=\psi_1(\alpha)+\psi_1(\bar\alpha)$, with $\psi_1$ the
[Hecke character](../gaussian/hecke-character.md) for $d=1$, that is $\psi_1(\alpha)=u(\alpha)\alpha$.

1. $P(-\alpha)=P(\alpha)$ and $P(\bar\alpha)=P(\alpha)$.
2. If $\alpha=x+yi$ with $x\equiv1$, $y\equiv0\pmod4$ or $x\equiv3$, $y\equiv2\pmod4$, then
   $P(\alpha)=2x$.
3. [Gauss's point count](gauss-point-count.md) holds.

**Proof sketch.** (1) $\psi_1(-\alpha)=\psi_1(\alpha)$
([Hecke character](../gaussian/hecke-character.md) (3)) and $\overline{-\alpha}=-\bar\alpha$;
conjugation swaps the two terms.

(2) Both $x+yi$ and $x-yi$ satisfy the hypothesis of
[primary unit](../gaussian/primary-unit.md) (5), so $u=1$ at both, and $P(\alpha)=\alpha+\bar\alpha$.

(3) Let $p\equiv1\pmod4$ be prime and take $A,B$ from
[Gauss's theorem](gauss-count.md); put $a=|A|$, $b=|B|$, so $a^2+b^2=p$, and $\pi_0=a+bi$. By
[the Gaussian primes above a split prime](../gaussian/norm-fibres-split.md) (g) and the invariance of $\psi_1$ under
units, $\sum_{\alpha\in A_p}\psi_1(\alpha)=4\psi_1(\pi_0)+4\psi_1(\bar\pi_0)=4P(\pi_0)$. According to
the signs of $A$ and $B$, $\pi_0$ is one of $\pm(-A-Bi)$ and $\pm\overline{(-A-Bi)}$, so
$P(\pi_0)=P(-A-Bi)$ by (1). From $A$ odd and $B\equiv A+1\pmod4$: $-A\equiv1$, $-B\equiv0$ or
$-A\equiv3$, $-B\equiv2\pmod4$, so $P(-A-Bi)=-2A$ by (2). Hence
$\frac14\sum_{A_p}u(\alpha)\alpha=-2A$, while
$p-\#\{y^2=x^3-x\}=p-(p+2A)=-2A$ by Gauss's theorem.

## Depends on

- [Gauss's point count on $y^2=x^3-x$](gauss-point-count.md)
- [The Hecke character $\psi_d$](../gaussian/hecke-character.md)

## Proof depends on

- [The primary unit of a Gaussian integer modulo 4](../gaussian/primary-unit.md)
- [The Gaussian primes above a split prime](../gaussian/norm-fibres-split.md)
- [Gauss's theorem on the points of $y^2=x^3-x$](gauss-count.md)

## Sources

- [The point count of Gauss](../../../../../sources/hecke-locators.md#the-point-count-of-gauss)
