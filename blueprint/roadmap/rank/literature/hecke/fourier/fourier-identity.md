---
article_id: af_fd3bf20ee595365676439363
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.CdFourier, ZInQ.Contrib.HeckeFE.cdFourier_of_oddGauss
---

# The Fourier identity for $\omega_d$

Let $\omega_d$ be the finite part of the [Hecke character](../gaussian/hecke-character.md) on
$(\mathbb Z/4d)^2$. The *Fourier identity* holds for $d$ if $\omega_d$ satisfies the Fourier relation of
[the functional equation of a periodic twist](../theta/twisted-functional-equation.md), with
$M=4d$ and constant
$$\kappa=4d\,(1+i)\left(\frac2d\right).$$
That is, $\hat\omega_d((1+i)\mu)=4d(1+i)\left(\frac2d\right)\omega_d(\mu)$ for every $\mu\in\mathbb Z^2$,
and $\hat\omega_d(\nu)=0$ whenever $\nu_1+\nu_2$ is odd.

If $d\equiv1\pmod4$ and [the odd Gauss sum identity](odd-gauss-sum.md) holds for $d$, then the
Fourier identity holds for $d$.

**Proof sketch.** $\hat\omega_d(\nu)=G_2(\nu)G_d(\nu)$ ([the factorization](fourier-factorization.md)
(4)), and $G_2(\nu)$ is the image of $g_2(\nu\bmod4)$ ([the 2-part](fourier-two-part.md) (2)). For
$\nu=(1+i)\mu$: $g_2=4(1+i)u(\mu)$ (the 2-part (3)), and
$G_d(\nu)=d\left(\frac{N(\nu)}d\right)=d\left(\frac{2N(\mu)}d\right)
=d\left(\frac2d\right)\left(\frac{N(\mu)}d\right)$ since $N((1+i)\mu)=2N(\mu)$; the product is
$4d(1+i)\left(\frac2d\right)\omega_d(\mu)$ by [the Hecke character](../gaussian/hecke-character.md) (1).
If $\nu_1+\nu_2$ is odd, $g_2(\nu\bmod4)=0$ by the 2-part (3).

## Depends on

- [The Hecke character $\psi_d$](../gaussian/hecke-character.md)
- [The functional equation of a periodic twist under a Fourier relation](../theta/twisted-functional-equation.md)
- [The odd part of the Fourier transform](odd-gauss-sum.md)

## Proof depends on

- [The Fourier transform of $\omega_d$ splits into a 2-part and an odd part](fourier-factorization.md)
- [The 2-part of the Fourier transform](fourier-two-part.md)

## Sources

- [Gauss and Jacobi sums](../../../../../sources/hecke-locators.md#gauss-and-jacobi-sums)
