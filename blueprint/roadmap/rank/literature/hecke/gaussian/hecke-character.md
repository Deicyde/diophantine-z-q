---
article_id: af_bb844af85b9d3abd0128f816
declaration: def
origin: background
statement: formalized
lean: ZInQ.Contrib.HeckeFE.psi, ZInQ.Contrib.HeckeFE.cdChar, ZInQ.Contrib.HeckeFE.cdChar_intCast, ZInQ.Contrib.HeckeFE.psi_mul, ZInQ.Contrib.HeckeFE.psi_units, ZInQ.Contrib.HeckeFE.psi_unit_mul, ZInQ.Contrib.HeckeFE.psi_gmul_unit, ZInQ.Contrib.HeckeFE.psi_split_prime
---

# The Hecke character $\psi_d$

For an integer $a$ and a natural number $n$, $\left(\frac an\right)$ is the Jacobi symbol: the
product of the Legendre symbols $\left(\frac ap\right)$ over the prime factors $p$ of $n$ counted
with multiplicity, where $\left(\frac a2\right)$ is $1$ for odd $a$ and $0$ for even $a$, and the
empty product (for $n=0,1$) is $1$. Let $d$ be a natural number and $u$ the
[primary unit](primary-unit.md). Gaussian integers are pairs as in
[Gaussian integers as pairs](norm-fibres.md). The *Hecke character* $\psi_d$ is the function on
$\mathbb Z[i]$
$$\psi_d(\alpha)=\left(\frac{N(\alpha)}{d}\right)u(\alpha)\,\alpha .$$
Its finite part is the function $\omega_d$ on $(\mathbb Z/4d)^2$
$$\omega_d(x)=\left(\frac{\tilde x_1^2+\tilde x_2^2}{d}\right)u(\tilde x_1\bmod4,\ \tilde x_2\bmod4),$$
where $\tilde x_1,\tilde x_2\in\{0,\dots,4d-1\}$ are the least residues of the coordinates of $x$.

1. If $d\ne0$, then $\omega_d(\alpha\bmod4d)=\left(\frac{N(\alpha)}{d}\right)u(\alpha)$ for every
   $\alpha\in\mathbb Z^2$; so $\psi_d(\alpha)=\omega_d(\alpha\bmod4d)\,\alpha$.
2. $\psi_d(\alpha\beta)=\psi_d(\alpha)\,\psi_d(\beta)$ for all $\alpha,\beta\in\mathbb Z[i]$.
3. $\psi_d(1)=\psi_d(-1)=\psi_d(i)=\psi_d(-i)=1$. Hence $\psi_d(i\alpha)=\psi_d(-\alpha)=\psi_d(\alpha)$,
   and $\psi_d(e\alpha)=\psi_d(\alpha)$ for every unit $e$.
4. If $p\equiv1\pmod4$ is prime and $p\nmid d$, then $\psi_d(p)=p$.

**Proof sketch.** (1) The Jacobi symbol depends on its numerator modulo $d$, and $u$ on residues
modulo $4$; both are determined modulo $4d$.

(2) The norm is multiplicative, the Jacobi symbol is multiplicative in its numerator, $u$ is
multiplicative ([primary unit](primary-unit.md) (1), (2)), and so is $\alpha\mapsto\alpha$.

(3) $\left(\frac1d\right)=1$, and the table gives $u(1)=1$, $u(-1)=-1$, $u(i)=-i$, $u(-i)=i$, so
$u(e)e=1$ for each unit. The rest follows from (2).

(4) $\left(\frac{p^2}{d}\right)=1$ because $p$ is coprime to $d$, and $u(p)=u(1,0)=1$ because
$p\equiv1\pmod4$.

## Depends on

- [The primary unit of a Gaussian integer modulo 4](primary-unit.md)
- [Gaussian integers as pairs, norms and units](norm-fibres.md)

## Sources

- [Deuring and the Hecke character](../../../../../sources/hecke-locators.md#deuring-and-the-hecke-character)
