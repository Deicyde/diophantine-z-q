---
article_id: af_40b9cec3cdf9ea158b29588b
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.iPow, ZInQ.Contrib.HeckeFE.cexp_two_pi_I_div_four, ZInQ.Contrib.HeckeFE.g2G, ZInQ.Contrib.HeckeFE.g2Sum_eq, ZInQ.Contrib.HeckeFE.g2G_table
---

# The 2-part of the Fourier transform

For $k\in\mathbb Z/4$ let $i^k\in\mathbb Z[i]$ be $i$ raised to the least residue of $k$. For
$n\in(\mathbb Z/4)^2$ put
$$g_2(n)=\sum_{a\in\{0,1,2,3\}^2}u_G(a)\,i^{a_1n_1+a_2n_2}\in\mathbb Z[i],$$
with $u_G$ the $\mathbb Z[i]$-valued [primary unit](../gaussian/primary-unit.md). Let $G_2$ be the
2-part of [the factorization](fourier-factorization.md).

1. $e^{2\pi im/4}=i^{m\bmod4}$ for every integer $m$.
2. For every $\nu\in\mathbb Z^2$, $G_2(\nu)$ is the image in $\mathbb C$ of $g_2(\nu\bmod4)$.
3. For all $m_1,m_2\in\mathbb Z/4$, $g_2(m_1-m_2,\,m_1+m_2)=4(1+i)\,u_G(m_1,m_2)$; and
   $g_2(n_1,n_2)=0$ whenever the least residue of $n_1+n_2$ is odd.

**Proof sketch.** (1) $e^{2\pi i/4}=i$ and $i^4=1$. (2) Termwise by (1) and
[primary unit](../gaussian/primary-unit.md) (1). (3) A finite computation in $\mathbb Z[i]$ over the
$16$ values of $n$ and the $16$ terms of each sum.

## Depends on

- [The primary unit of a Gaussian integer modulo 4](../gaussian/primary-unit.md)
- [The Fourier transform of $\omega_d$ splits into a 2-part and an odd part](fourier-factorization.md)

## Sources

- [Gauss and Jacobi sums](../../../../../sources/hecke-locators.md#gauss-and-jacobi-sums)
