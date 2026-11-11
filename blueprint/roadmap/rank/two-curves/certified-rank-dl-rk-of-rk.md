---
article_id: af_c87f730606b0c78cabb5889b
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.certifiedRankDLRk_of_certifiedRankRk, ZInQ.RouteK.Rank.slots_d₂_facts
---

# CR₃^DL,Rk from CR₃^Rk

The hypothesis CR₃^Rk implies CR₃^DL,Rk.

Along the way: let $\beta,\theta,p_0$ satisfy the hypotheses of CR₃^DL,Rk, let $q_0$, $r_p$,
$r_\ell$ be any slot data for $\beta,\theta,p_0$, and let
$d_1=|\beta|\,q_0\prod_pr_p\prod_\ell r_\ell$. Then $d_1|\theta|$ is squarefree,
$d_1|\theta|\equiv5\pmod8$, $\beta$ divides $d_1|\theta|$, and $(d_1|\theta|,\beta)$ carries a
Selmer certificate.

**Proof sketch.** *Along the way.* By the realization, $d_2=d_1\theta=d_1|\theta|$ is squarefree
and $(d_2,\beta)$ carries a Selmer certificate. Also $d_1\equiv5$ and $\theta\equiv1\pmod8$, so
$d_1|\theta|\equiv5\pmod8$; and $\beta\mid d_1$, so $\beta\mid d_1|\theta|$.

*The implication.* Let $\beta,\theta,p_0$ satisfy the hypotheses of CR₃^DL,Rk. Then $\beta$ is
odd, $\theta$ is odd (because $\theta\equiv1\pmod8$), they are coprime and $p_0\in P(\beta)$, so
slot data exist; take any. By the realization, $d_1$ is squarefree with $d_1\equiv5\pmod8$,
$\beta\mid d_1$, and $(d_1,\beta)$ carries a Selmer certificate; the statement along the way gives
the same for $d_1|\theta|$. Since $\beta$ is squarefree, the lemma on the 2-Selmer group of a
certified curve, with $a=\beta$, gives on each of the two curves $|\mathrm{Sel}_2|=8$ and a class
$(\beta,b)\in\mathrm{Sel}_2$, with $|\beta|\equiv7\pmod8$. CR₃^Rk then gives a point of infinite
order on each curve.

## Depends on

- [The positive-rank hypothesis on the two curves of a slot choice](certified-rank-dl-rk.md)
- [The certified rank hypothesis in positive-rank form](../certified-rank-rk.md)
- [The configuration of an odd number and Selmer certificates](../../route-k/prime-configuration.md)
- [The slot conditions](../../route-k/slot-conditions.md)
- [The realization: both curves reduce to the base configuration](../../route-k/realization.md)

## Proof depends on

- [The 2-Selmer group of a certified curve](selmer-group-of-a-certificate.md)
- [The slots exist](../../route-k/slots.md)

## Sources

- [Positive rank on the two curves](../../../sources/rank-locators.md#positive-rank-on-the-two-curves)
