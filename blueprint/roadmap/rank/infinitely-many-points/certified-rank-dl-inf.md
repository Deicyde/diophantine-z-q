---
article_id: af_989f05465efb622d59a39d4b
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank.CertifiedRankDLInf
---

# The infinitely-many-points hypothesis on the two curves of a slot choice

The hypothesis CR₃^DL,Inf is the following assertion. Let $\beta,\theta$ be integers and $p_0$ a
natural number such that:

- $\beta$ is odd and squarefree with $|\beta|\equiv7\pmod8$, and $p_0$ is a prime dividing
  $\beta$;
- $\theta>0$ is squarefree with $\theta\equiv1\pmod8$;
- $\beta$ and $\theta$ are coprime;
- $[\beta/\ell]=0$ for every prime $\ell\mid\theta$, and $[\theta/p]=0$ for every prime
  $p\mid\beta$.

Then there are slot data $q_0$, $r_p$ ($p\in P(\beta)\setminus\{p_0\}$) and $r_\ell$
($\ell\in P(\theta)$) for $\beta,\theta,p_0$, satisfying [the slot conditions](../../route-k/slot-conditions.md),
such that, with
$$d_1=|\beta|\,q_0\prod_{p}r_p\prod_{\ell}r_\ell ,$$
both $y^2=x^3-d_1^2x$ and $y^2=x^3-(d_1|\theta|)^2x$ have infinitely many rational solutions
$(x,y)\in\mathbb Q^2$.

The premises are those of [CR₃^DL,Rk](../two-curves/certified-rank-dl-rk.md); only the conclusion
changes, from points of infinite order on the two curves to infinitely many rational solutions of
their equations, which mentions no group law. The assertion still depends on the slot conditions,
so a change to the slot construction changes what it asserts. The two hypotheses are equivalent.
Since CR₃^DL,Rk follows from [CR₃^Rk](../two-curves/certified-rank-dl-rk-of-rk.md) and from
[CR₃^TYZ,Rk](../two-curves/certified-rank-dl-rk-of-tyz-rk.md), the equivalences make CR₃^DL,Inf
follow from CR₃^Inf and from CR₃^TYZ,Inf, so it rests on the same theorems:
Tian–Yuan–Zhang as completed by Proposition N, which is not refereed, and Gross–Zagier with an
auxiliary field. It is a
hypothesis, not proved here.

## Depends on

- [The realization: both curves reduce to the base configuration](../../route-k/realization.md)
- [The slot conditions](../../route-k/slot-conditions.md)
- [Residue bits](../../route-k/residue-bits.md)
- [Infinitely many rational solutions of $y^2=x^3-d^2x$](infinitely-many-points.md)

## Sources

- [The infinitely-many-points forms](../../../sources/rank-locators.md#the-infinitely-many-points-forms)
- [The two curves of a slot choice](../../../sources/rank-locators.md#the-two-curves-of-a-slot-choice)
- [Tian-Yuan-Zhang](../../../sources/rank-locators.md#tian-yuan-zhang)
- [Gross-Zagier](../../../sources/rank-locators.md#gross-zagier)
- [The trust statement for CR3](../../../sources/route-k-locators.md#the-trust-statement-for-cr3)
