---
article_id: af_8840c820a588a8783b887fbf
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.mordellWeilE
---

# Mordell-Weil for $E/K_0$ from the descent

The group $E(K_0)$ is finitely generated; that is, the Mordell-Weil hypothesis for the
generator curve holds.

This is not part of the manuscript's argument, which cites the Mordell-Weil theorem. It
shows that, given the descent index already proved in this chapter, the hypothesis can be
discharged by the classical descent theorem.

**Proof sketch.** (Silverman, Theorem VIII.3.1 and Section VIII.6.) Let $h$ be the naive
height $h(P)=\sum_v\log\max(1,|x(P)|_v)$ on $E(K_0)$, $h(O)=0$, the sum over the places of the
number field $K_0$ with their usual normalization. Then $h\ge0$; there is a constant $c$ with
$|h(P+Q)+h(P-Q)-2h(P)-2h(Q)|\le c$ for all $P,Q$ (the approximate parallelogram law); and for
every bound $B$ only finitely many $P$ have $h(P)\le B$ (Northcott's property for $K_0$, since
each $x$-coordinate determines at most two points). The descent theorem says that an abelian
group with such a height and finite $G/2G$ is finitely generated: elements of height below
an explicit bound, together with representatives of $G/2G$, generate. Here
$[E(K_0):2E(K_0)]=8$ is finite by the descent index.

## Depends on

- [Mordell–Weil for the generator curve](../../main/mordell-weil.md)

## Proof depends on

- [The index $[E(K_0):2E(K_0)]=8$](descent-index.md)

## Sources

- [Rank and odd index](../../../sources/model-locators.md#rank-and-odd-index)
- [Silverman](../../../sources/model-locators.md#silverman)
