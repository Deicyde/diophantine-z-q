---
article_id: af_55f95fb300855e14d4e97cba
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.poleCompleteness_of_certifiedRankDLAdmRk
---

# Pole completeness from CR₃^DL,Adm,Rk

Assume CR₃^DL,Adm,Rk. Then pole completeness holds: every admissible $B$ satisfies $\Phi(B)$.

**Proof sketch.** By the reformulation through admissible inputs, it suffices to treat an
admissible $B$. Take $m$, $p_0$ and the slot data from the hypothesis, and put
$\beta=\mathrm{sqf}(mB)$, $\theta=\mathrm{sqf}(m(m-B))$. Since $\beta$ is odd with
$|\beta|\equiv7\pmod8$ and $p_0\mid\beta$, (θ1)–(θ4) show, as in the descent lemma, that
$\beta,\theta,p_0$ satisfy the hypotheses of CR₃^DL,Rk. The one-input form of pole completeness
from CR₃^DL,Rk, applied to the two points of infinite order, then gives $\Phi(B)$.

## Depends on

- [The positive-rank hypothesis at the inputs of admissible numbers](certified-rank-dl-adm-rk.md)
- [Pole completeness](../../main/pole-completeness.md)

## Proof depends on

- [Pole completeness from CR₃^DL,Rk](pole-completeness-from-dl-rk.md)
- [The descent lemma](../../route-k/descent-lemma.md)
- [Admissible inputs, the squarefree part, $\beta$ and $\theta$](../../route-k/squarefree-part.md)

## Sources

- [The two curves of a slot choice](../../../sources/rank-locators.md#the-two-curves-of-a-slot-choice)
