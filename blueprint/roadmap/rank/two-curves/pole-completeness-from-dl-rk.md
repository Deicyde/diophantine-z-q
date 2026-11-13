---
article_id: af_694426e2d167b37e12c64795
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.poleCompleteness_of_certifiedRankDLRk, ZInQ.RouteK.Rank.poleSoluble_of_slots_infinite_order
---

# Pole completeness from CR₃^DL,Rk

Assume CR₃^DL,Rk. Then pole completeness holds: every admissible $B$ satisfies $\Phi(B)$.

For a single input: let $B$ be admissible, $m$ a signed divisor of $2730$,
$\beta=\mathrm{sqf}(mB)$ and $\theta=\mathrm{sqf}(m(m-B))$, and let $p_0$ be a natural number such
that $\beta,\theta,p_0$ satisfy the hypotheses of CR₃^DL,Rk. If for some slot data
$q_0$, $r_p$, $r_\ell$ for $\beta,\theta,p_0$, with $d_1=|\beta|\,q_0\prod_pr_p\prod_\ell r_\ell$,
both $C_{d_1}(\mathbb Q)$ and $C_{d_1|\theta|}(\mathbb Q)$ have points of infinite order, then
$\Phi(B)$ holds.

**Proof sketch.** *One input.* By the realization, $d_1$ is squarefree with $d_1\equiv5\pmod8$,
$\beta\mid d_1$, and $(d_1,\beta)$ carries a Selmer certificate; by the facts proved along the way
to CR₃^DL,Rk from CR₃^Rk, the same holds for $d_1|\theta|$. Also $\beta$ is squarefree with
$|\beta|\equiv7\pmod8$. The lemma on a point of infinite order on a certified curve, with
$a=\beta$, gives a point $(x_1,y_1)$ on $C_{d_1}$ and a point $(x_2,y_2)$ on $C_{d_1|\theta|}$,
with $x_i\ne0$ and $x_i/\beta$ squares. Since $0<B<1/2$, the integer $m$ is not $B$. Take
$N=d_1\ne0$. Then $C_{N\theta}$ is $C_{d_1|\theta|}$, since $(d_1|\theta|)^2=(d_1\theta)^2$, and
the lemma on points and pole solubility gives $\Phi(B)$.

*Pole completeness.* By the reformulation through admissible inputs, it suffices to treat an
admissible $B$. The multiplier lemma in its combined form with the existence of the slots, of
which only the multiplier part is used here, gives a signed divisor $m$ of $2730$ with $\beta$ odd
and $|\beta|\equiv7\pmod8$, and a prime factor $p_0$ of $\beta$. By the descent lemma's facts
about admissible inputs, which rest on (θ1)–(θ4), the triple $\beta,\theta,p_0$ satisfies the
hypotheses of CR₃^DL,Rk. CR₃^DL,Rk gives slot data whose two curves have points of infinite order, and the
first part gives $\Phi(B)$. Unlike the proof from CR₃, the slot data come from the hypothesis,
not from the descent lemma; of the descent lemma only the facts about admissible inputs are used.

## Depends on

- [The positive-rank hypothesis on the two curves of a slot choice](certified-rank-dl-rk.md)
- [Pole completeness](../../main/pole-completeness.md)
- [Admissible inputs, the squarefree part, $\beta$ and $\theta$](../../route-k/squarefree-part.md)
- [The slot conditions](../../route-k/slot-conditions.md)
- [The realization: both curves reduce to the base configuration](../../route-k/realization.md)

## Proof depends on

- [A point of infinite order on a certified curve](point-of-infinite-order.md)
- [CR₃^DL,Rk from CR₃^Rk](certified-rank-dl-rk-of-rk.md)
- [Points on two congruent number curves give pole solubility](../../route-k/points-pole-solubility.md)
- [The slots exist](../../route-k/slots.md)
- [The descent lemma](../../route-k/descent-lemma.md)

## Sources

- [The two curves of a slot choice](../../../sources/rank-locators.md#the-two-curves-of-a-slot-choice)
- [Positive rank on the two curves](../../../sources/rank-locators.md#positive-rank-on-the-two-curves)
- [Points and the pole polynomial](../../../sources/route-k-locators.md#points-and-the-pole-polynomial)
