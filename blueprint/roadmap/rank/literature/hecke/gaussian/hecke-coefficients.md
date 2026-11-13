---
article_id: af_6689ba4a10b187daf549bed6
declaration: def
origin: background
statement: formalized
lean: ZInQ.Contrib.HeckeFE.heckeCoeff, ZInQ.Contrib.HeckeFE.heckeCoeff_eq_sum_psi, ZInQ.Contrib.HeckeFE.heckeCoeff_zero, ZInQ.Contrib.HeckeFE.heckeCoeff_one, ZInQ.Contrib.HeckeFE.heckeCoeff_prime_twist
---

# The coefficients of the Hecke L-series $L(\psi_d,s)$

For natural numbers $d$ and $n$ the *Hecke coefficient* is
$$\lambda_d(n)=\frac14\sum_{\alpha\in A_n}\left(\frac{N(\alpha)}{d}\right)u(\alpha)\,\alpha
=\frac14\sum_{\alpha\in A_n}\psi_d(\alpha),$$
with $A_n$ the [Gaussian integers of norm $n$](norm-fibres.md), $u$ the
[primary unit](primary-unit.md) and $\psi_d$ the [Hecke character](hecke-character.md). The factor
$\frac14$ accounts for the four generators of each ideal of $\mathbb Z[i]$; the Dirichlet series
with these coefficients is the Hecke L-series $L(\psi_d,s)$ (motivation only; no L-series of a
Hecke character is defined here).

1. $\lambda_d(0)=0$ and $\lambda_d(1)=1$.
2. For all natural numbers $d$ and $p$, $\lambda_d(p)=\left(\frac pd\right)\lambda_1(p)$.

**Proof sketch.** (1) $A_0=\{0\}$, whose term is $0$. $A_1$ is the set of the four units, on which
$\psi_d=1$ ([Hecke character](hecke-character.md) (3)), so the sum is $4$.

(2) Every $\alpha\in A_p$ has $N(\alpha)=p$, so the symbol $\left(\frac{N(\alpha)}d\right)$ is the
constant $\left(\frac pd\right)$; and $\left(\frac{N(\alpha)}1\right)=1$.

## Depends on

- [Gaussian integers as pairs, norms and units](norm-fibres.md)
- [The primary unit of a Gaussian integer modulo 4](primary-unit.md)
- [The Hecke character $\psi_d$](hecke-character.md)

## Sources

- [Deuring and the Hecke character](../../../../../sources/hecke-locators.md#deuring-and-the-hecke-character)
