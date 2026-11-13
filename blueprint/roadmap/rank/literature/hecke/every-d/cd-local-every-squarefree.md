---
article_id: af_a1d5c246d45242cd4e17f4cb
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeAll.isMinimal_cdLocal', ZInQ.Contrib.HeckeAll.hasAdditiveReduction_cdLocal', ZInQ.Contrib.HeckeAll.localPolynomial_cdLocal_of_dvd', ZInQ.Contrib.HeckeAll.localPolynomial_cdLocal_eq'
---

# The local factors of $C_d$ for every squarefree $d$

Let $v$ be a finite place of $\mathbb Q$ with prime $p=p_v$, $C_{d,v}$
[the curve $C_d$ over $\mathbb Q_v$](../../l-function-cd/cd-local.md), reduction types and local
polynomials as in [the local polynomial](../../l-function-cd/local-polynomial.md), and $P_{d,p}$
[the Euler polynomial](../../l-function-cd/cd-euler-polynomial.md). Let $d$ be squarefree, odd or
even.

1. $C_{d,v}$ is minimal over $\mathcal O_v$.
2. If $p\mid2d$, then $C_{d,v}$ has additive reduction, and its local polynomial is $1$.
3. The local polynomial of $C_{d,v}$ is $P_{d,p}$.

**Proof sketch.** (1) If $p=2$ and $d$ is even, then $d=2e$ with $e$ odd (as $d$ is squarefree),
and [minimality at $2$](minimal-at-two.md) (4) applies. Otherwise $p^{12}\nmid(2d)^6$: for $p=2$
because $d$ is odd, and for odd $p$ because $p^2\mid(2d)$ would give $p^2\mid d$. So the discriminant
criterion of [minimal Weierstrass equations](../../l-function-cd/minimal-models.md) (1) applies, as
in [minimality and reduction type](../../l-function-cd/cd-reduction.md) (2).

(2) Minimal by (1); the discriminant $(2d)^6$ and $c_4=48d^2=2d\cdot24d$ lie in $\mathfrak m_v$.
An additive minimal equation with nonzero discriminant has local polynomial $1$
([the local polynomial](../../l-function-cd/local-polynomial.md)).

(3) For $p\mid2d$ by (2); for $p\nmid2d$ by
[the local polynomial of $C_d$](../../l-function-cd/cd-local-polynomial.md), which holds for every
$d$ at such $p$.

## Depends on

- [The curve $C_d$ over a completion of $\mathbb Q$](../../l-function-cd/cd-local.md)
- [The local polynomial from any minimal equation](../../l-function-cd/local-polynomial.md)
- [The Euler polynomial of $C_d$ at $p$](../../l-function-cd/cd-euler-polynomial.md)

## Proof depends on

- [Minimality of $C_d$ at $2$ for even squarefree $d$](minimal-at-two.md)
- [Minimal Weierstrass equations over a discrete valuation ring](../../l-function-cd/minimal-models.md)
- [Minimality and reduction type of $C_d$ at each prime](../../l-function-cd/cd-reduction.md)
- [The local polynomial of $C_d$ at each prime](../../l-function-cd/cd-local-polynomial.md)

## Sources

- [The curves for even and non-squarefree d](../../../../../sources/hecke-locators.md#the-curves-for-even-and-non-squarefree-d)
- [The L-series of the congruent number curves](../../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
