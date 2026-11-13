---
article_id: af_29ea2ec96abbaf4cb3142d8b
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Literature.not_dvd_two_mul_pow_six, ZInQ.Literature.isMinimal_cdLocal, ZInQ.Literature.hasGoodReduction_cdLocal, ZInQ.Literature.hasAdditiveReduction_cdLocal, ZInQ.Literature.natCard_point_reduction_cdLocal
---

# Minimality and reduction type of $C_d$ at each prime

Let $v$ be a finite place of $\mathbb Q$ with prime $p=p_v$, and $C_{d,v}$ the
[curve $C_d$ over $\mathbb Q_v$](cd-local.md). Reduction types are those of
[the local polynomial](local-polynomial.md).

1. For every prime number $\ell$ and every odd squarefree $d$, $\ell^{12}\nmid(2d)^6$.
2. If $d$ is odd and squarefree, then $C_{d,v}$ is minimal over $\mathcal O_v$, for every $v$.
3. For every natural number $d$ with $p\nmid2d$, $C_{d,v}$ is minimal and has good reduction.
4. If $d$ is odd and squarefree and $p\mid2d$, then $C_{d,v}$ is minimal and has additive
   reduction.
5. For every natural number $d$ with $p\nmid2d$, if $C_{d,v}$ is minimal (which holds by (3)), then
   the reduction of $C_{d,v}$ has as many points over $\kappa_v$ as the curve
   $y^2=x^3-d^2x$ has over $\mathbb F_p=\mathbb Z/p\mathbb Z$, the point at infinity included in
   both counts.

**Proof sketch.** (1) If $\ell^{12}\mid(2d)^6$, then $(\ell^2)^6\mid(2d)^6$, so $\ell^2\mid2d$. Since
$d$ is odd and squarefree, $2d$ is squarefree, so $\ell$ would be a unit, which it is not.

(2) By [the curve over $\mathbb Q_v$](cd-local.md) (1) and (2), $C_{d,v}$ comes from the model over
$\mathcal O_v$, whose discriminant is $(2d)^6$. By [the places of $\mathbb Q$](completion.md) (4),
$(2d)^6\in\mathfrak m_v^{12}$ exactly when $p^{12}\mid(2d)^6$, which (1) with $\ell=p$ excludes. So
[minimal Weierstrass equations](minimal-models.md) (1) applies.

(3) $p\nmid2d$ gives $2d\notin\mathfrak m_v$, so $(2d)^6\notin\mathfrak m_v$ as $\mathfrak m_v$ is
prime, and a fortiori $(2d)^6\notin\mathfrak m_v^{12}$: the equation is minimal as in (2). Its
discriminant is a unit of $\mathcal O_v$, so its valuation is $0$: good reduction.

(4) Minimal by (2). From $p\mid2d$, the discriminant $(2d)^6$ lies in $\mathfrak m_v$, and so does
$c_4=48d^2=2d\cdot24d$; both have positive valuation, which is additive reduction.

(5) By the curve over $\mathbb Q_v$ (4) the reduction is the model over $\kappa_v$; its
discriminant, the reduction of $(2d)^6$, is nonzero since $(2d)^6\notin\mathfrak m_v$. Transport
along the isomorphism $\kappa_v\cong\mathbb Z/p\mathbb Z$ of the places of $\mathbb Q$ (6), which
maps the model to the model, and apply [point counts](point-counts.md) (5).

## Depends on

- [The curve $C_d$ over a completion of $\mathbb Q$](cd-local.md)
- [The local polynomial from any minimal equation](local-polynomial.md)

## Proof depends on

- [Minimal Weierstrass equations over a discrete valuation ring](minimal-models.md)
- [The places of $\mathbb Q$ and their completions](completion.md)
- [Point counts under changes of variables and field isomorphisms](point-counts.md)

## Sources

- [The L-series of the congruent number curves](../../../../sources/rank-locators.md#the-l-series-of-the-congruent-number-curves)
- [Minimal equations over a discrete valuation ring](../../../../sources/rank-locators.md#minimal-equations-over-a-discrete-valuation-ring)
