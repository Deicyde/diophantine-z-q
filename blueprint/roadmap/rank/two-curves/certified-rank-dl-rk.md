---
article_id: af_76d92f1e4aa64d92cf26c8ca
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Rank.CertifiedRankDLRk
---

# The positive-rank hypothesis on the two curves of a slot choice

The hypothesis CR₃^DL,Rk is the following assertion. Let $\beta,\theta$ be integers and $p_0$ a
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
both $C_{d_1}(\mathbb Q)$ and $C_{d_1|\theta|}(\mathbb Q)$ contain a point of infinite order. Here
$C_d$ is the curve $y^2=x^3-d^2x$.

The hypotheses on $\beta,\theta,p_0$ are those of [the realization](../../route-k/realization.md),
which the multiplier lemma and (θ1)–(θ4) give for an admissible input. By the realization,
$d_1$ and $d_1|\theta|=d_1\theta=d_2$ are squarefree and $\equiv5\pmod8$, $\beta$ divides both,
and both $(d_1,\beta)$ and $(d_2,\beta)$ carry Selmer certificates. So these are the two curves at
which the proof of pole completeness applies the rank hypothesis, and both have 2-Selmer groups
of order $8$. The slot data are existential: points of infinite order on the two curves of any
one slot choice suffice. The assertion depends on the slot conditions, so a change to the slot
construction changes what it asserts.

CR₃^DL,Rk is not proved here; it is a hypothesis. It follows from CR₃^Rk and from CR₃^TYZ,Rk, so
it rests on the same theorems: Tian–Yuan–Zhang as completed by Proposition N, which is not
refereed, and Gross–Zagier with an auxiliary field.

## Depends on

- [The realization: both curves reduce to the base configuration](../../route-k/realization.md)
- [The slot conditions](../../route-k/slot-conditions.md)
- [Residue bits](../../route-k/residue-bits.md)

## Sources

- [The two curves of a slot choice](../../../sources/rank-locators.md#the-two-curves-of-a-slot-choice)
- [Tian-Yuan-Zhang](../../../sources/rank-locators.md#tian-yuan-zhang)
- [Gross-Zagier](../../../sources/rank-locators.md#gross-zagier)
- [The trust statement for CR3](../../../sources/route-k-locators.md#the-trust-statement-for-cr3)
