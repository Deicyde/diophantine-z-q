---
article_id: af_af05baaa2ef3ca186d19504a
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank.CertifiedRankDLAdmRk
---

# The positive-rank hypothesis at the inputs of admissible numbers

The hypothesis CR₃^DL,Adm,Rk is the following assertion. For every admissible $B$ there are:

- a signed divisor $m$ of $2730$ such that $\beta=\mathrm{sqf}(mB)$ is odd with
  $|\beta|\equiv7\pmod8$;
- a prime $p_0$ dividing $\beta$;
- slot data $q_0$, $r_p$ ($p\in P(\beta)\setminus\{p_0\}$) and $r_\ell$ ($\ell\in P(\theta)$) for
  $\beta$, $\theta=\mathrm{sqf}(m(m-B))$ and $p_0$, satisfying
  [the slot conditions](../../route-k/slot-conditions.md);

such that, with $d_1=|\beta|\,q_0\prod_pr_p\prod_\ell r_\ell$, both $C_{d_1}(\mathbb Q)$ and
$C_{d_1|\theta|}(\mathbb Q)$ contain a point of infinite order. Here $C_d$ is the curve
$y^2=x^3-d^2x$.

These are the data that the multiplier lemma and the existence of the slots produce for an
admissible input. So CR₃^DL,Adm,Rk asks for the points only at the inputs that admissible numbers
produce, while CR₃^DL,Rk asks for them at every triple $\beta,\theta,p_0$ satisfying the hypotheses
of the realization. Like CR₃^DL,Rk, it depends on the slot conditions and on the definitions of
admissibility, $\beta$ and $\theta$.

CR₃^DL,Adm,Rk is not proved here; it is a hypothesis, implied by CR₃^DL,Rk.

## Depends on

- [Admissible inputs, the squarefree part, $\beta$ and $\theta$](../../route-k/squarefree-part.md)
- [The slot conditions](../../route-k/slot-conditions.md)
- [The realization: both curves reduce to the base configuration](../../route-k/realization.md)
- [Residue bits](../../route-k/residue-bits.md)

## Sources

- [The two curves of a slot choice](../../../sources/rank-locators.md#the-two-curves-of-a-slot-choice)
