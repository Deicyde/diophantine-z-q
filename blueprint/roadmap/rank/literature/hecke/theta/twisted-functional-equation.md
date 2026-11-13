---
article_id: af_4ec99ec48a7613a688b2ac36
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.fourierHat, ZInQ.Contrib.HeckeFE.lambdaC, ZInQ.Contrib.HeckeFE.differentiable_lambdaC, ZInQ.Contrib.HeckeFE.lambdaC_eq, ZInQ.Contrib.HeckeFE.dual_eq, ZInQ.Contrib.HeckeFE.FourierRel, ZInQ.Contrib.HeckeFE.fourierRel_const_mul, ZInQ.Contrib.HeckeFE.mulOneAddI, ZInQ.Contrib.HeckeFE.mulOneAddI_injective, ZInQ.Contrib.HeckeFE.fourier_tsum_eq, ZInQ.Contrib.HeckeFE.lambdaC_two_sub
---

# The functional equation of a periodic twist under a Fourier relation

Let $M\ge1$, $c:(\mathbb Z/M)^2\to\mathbb C$, and $T_c$ the
[twisted lattice series](twisted-series.md), with the notation there; $j$ runs over
$\{0,\dots,M-1\}^2$. Define
$$\hat c(\nu)=\sum_jc(j)\,e^{2\pi i(j_1\nu_1+j_2\nu_2)/M}\quad(\nu\in\mathbb Z^2),\qquad
\Lambda_c(s)=\sum_jc(j)\,\Lambda_{j_1/M,\,j_2/M}(s),$$
with $\Lambda_{a,b}$, $\Lambda^*_{a,b}$ the [completed lattice functions](theta-mellin.md). For
$\mu\in\mathbb Z^2$ let $(1+i)\mu=(\mu_1-\mu_2,\mu_1+\mu_2)$, the product with $1+i$ in
$\mathbb Z[i]$. For $\kappa\in\mathbb C$, $c$ satisfies the *Fourier relation with constant
$\kappa$* if $\hat c((1+i)\mu)=\kappa\,c(\mu)$ for every $\mu\in\mathbb Z^2$ and $\hat c(\nu)=0$ for
every $\nu$ with $\nu_1+\nu_2$ odd.

1. $\Lambda_c$ is entire.
2. For $\operatorname{Re}s>3/2$: $\pi^{-s}\Gamma(s)\,T_c(s)=M\,(M^2)^{-s}\,\Lambda_c(s)$.
3. For $\operatorname{Re}s>3/2$:
   $\displaystyle\sum_jc(j)\,\Lambda^*_{j_1/M,\,j_2/M}(s)=\pi^{-s}\Gamma(s)\,(-i)\sum_{\nu\in\mathbb Z^2}\frac{\hat c(\nu)\,\nu}{N(\nu)^s}$,
   the last sum read as $0$ where the family is not summable.
4. If $c$ satisfies the Fourier relation with constant $\kappa$, so does $r\,c$ for every
   $r\in\mathbb C$, with the same $\kappa$.
5. $\mu\mapsto(1+i)\mu$ is injective on $\mathbb Z^2$.
6. If $c$ satisfies the Fourier relation with constant $\kappa$, then for every $s\in\mathbb C$
   $$\sum_{\nu\in\mathbb Z^2}\frac{\hat c(\nu)\,\nu}{N(\nu)^s}=\kappa(1+i)\,2^{-s}\,T_c(s).$$
7. If $c$ satisfies the Fourier relation with constant $\kappa$, then for every $s\in\mathbb C$
   $$\Lambda_c(2-s)=-i\kappa(1+i)\,2^{-s}\,M\,(M^2)^{-s}\,\Lambda_c(s).$$

**Proof sketch.** (1) A finite linear combination of the entire functions
$\Lambda_{j_1/M,j_2/M}$ ([completed lattice functions](theta-mellin.md) (3)).

(2) Expand $T_c$ by [periodic twists](twisted-series.md) (2) and each $L_{j/M}(s)$ by
$\pi^{-s}\Gamma(s)L_{j/M}(s)=\Lambda_{j/M}(s)$ ([the lattice Dirichlet series](lattice-series.md)
(4)).

(3) Expand each $\Lambda^*_{j/M}(s)$ by the lattice Dirichlet series (4), multiply by $c(j)$, sum the
finitely many summable families, and collect $\sum_jc(j)e^{2\pi i(j_1\nu_1+j_2\nu_2)/M}=\hat c(\nu)$.

(4) $\widehat{rc}=r\hat c$.

(5) $\mu_1-\mu_2$ and $\mu_1+\mu_2$ determine $\mu$.

(6) Every term with $\nu_1+\nu_2$ odd vanishes. If $\nu_1+\nu_2=2k$, then $\nu=(1+i)\mu$ with
$\mu=(k,k-\nu_1)$. So the family is supported on the image of the injective map (5), and the sum
may be taken over $\mu$. There $\hat c((1+i)\mu)=\kappa c(\mu)$, the Gaussian integer $(1+i)\mu$ is
$(1+i)$ times $\mu$, and $N((1+i)\mu)=2N(\mu)$, so $N((1+i)\mu)^{-s}=2^{-s}N(\mu)^{-s}$.

(7) For $\operatorname{Re}s>3/2$:
$\Lambda_c(2-s)=\sum_jc(j)\Lambda_{j/M}(2-s)=\sum_jc(j)\Lambda^*_{j/M}(s)$ by
[completed lattice functions](theta-mellin.md) (4); by (3) and (6) this is
$\pi^{-s}\Gamma(s)(-i)\kappa(1+i)2^{-s}T_c(s)$, and (2) turns $\pi^{-s}\Gamma(s)T_c(s)$ into
$M(M^2)^{-s}\Lambda_c(s)$. Both sides of (7) are entire functions of $s$ that agree on the open set
$\operatorname{Re}s>3/2$, a neighbourhood of $2$; by the identity theorem they agree on
$\mathbb C$.

## Depends on

- [Periodic twists of the lattice series and their continuation](twisted-series.md)
- [The completed lattice functions and their functional equation](theta-mellin.md)

## Proof depends on

- [The lattice Dirichlet series and its entire continuation](lattice-series.md)

## Sources

- [Theta series and the method of Hecke](../../../../../sources/hecke-locators.md#theta-series-and-the-method-of-hecke)
