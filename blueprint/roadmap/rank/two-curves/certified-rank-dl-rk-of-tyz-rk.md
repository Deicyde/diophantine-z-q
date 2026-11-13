---
article_id: af_b4eebcf586b36379613785c3
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.certifiedRankDLRk_of_certifiedRankTYZRk, ZInQ.RouteK.Rank.exists_infinite_order_of_certifiedRankTYZRk_of_selmerCertified
---

# CR₃^DL,Rk from CR₃^TYZ,Rk

The hypothesis CR₃^TYZ,Rk implies CR₃^DL,Rk.

For a single curve: assume CR₃^TYZ,Rk, let $d$ be a squarefree natural number with
$d\equiv5\pmod8$, and let $a$ be a squarefree integer dividing $d$ with $|a|\equiv7\pmod8$ such
that $(d,a)$ carries a Selmer certificate. Then $C_d(\mathbb Q)$ has a point of infinite order.

**Proof sketch.** *One curve.* The lemma on the 2-Selmer group of a certified curve gives
$|\mathrm{Sel}_2(C_d)|=8$ and some $(a,b)\in\mathrm{Sel}_2(C_d)$. Since $|a|\equiv7\pmod8$,
Corollary 4.4 gives $\det M_{5b}=1$. By Theorem 3.6, $\det M_{5b}=T_{5b}(d)$, so $T_{5b}(d)=1$,
and CR₃^TYZ,Rk gives the point.

*The two curves.* Let $\beta,\theta,p_0$ satisfy the hypotheses of CR₃^DL,Rk. Then $\beta,\theta$
are odd and coprime and $p_0\in P(\beta)$, so slot data exist; take any. By the realization,
$d_1$ is squarefree with $d_1\equiv5\pmod8$, $\beta\mid d_1$, and $(d_1,\beta)$ carries a Selmer
certificate; by the facts proved along the way to CR₃^DL,Rk from CR₃^Rk, the same holds for
$d_1|\theta|$. Since $\beta$ is squarefree with $|\beta|\equiv7\pmod8$, the one-curve statement
with $a=\beta$ applies to both curves.

## Depends on

- [The positive-rank hypothesis on the two curves of a slot choice](certified-rank-dl-rk.md)
- [The Tian–Yuan–Zhang hypothesis in positive-rank form](../certified-rank-tyz-rk.md)
- [The configuration of an odd number and Selmer certificates](../../route-k/prime-configuration.md)

## Proof depends on

- [The 2-Selmer group of a certified curve](selmer-group-of-a-certificate.md)
- [CR₃^DL,Rk from CR₃^Rk](certified-rank-dl-rk-of-rk.md)
- [A first coordinate congruent to 7 forces $\det M_{5b}=1$ (Corollary 4.4)](../../rank-5b/corollary-4-4.md)
- [Row 5b of Smith's table (Theorem 3.6)](../../rank-5b/genus-sum/theorem-3-6.md)
- [The slots exist](../../route-k/slots.md)
- [The realization: both curves reduce to the base configuration](../../route-k/realization.md)

## Sources

- [Positive rank on the two curves](../../../sources/rank-locators.md#positive-rank-on-the-two-curves)
- [Corollary 4.4](../../../sources/rank-5b-locators.md#corollary-44)
- [Theorem 3.6](../../../sources/rank-5b-locators.md#theorem-36)
