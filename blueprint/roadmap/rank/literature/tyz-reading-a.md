---
article_id: af_0181f4dd06d1590d7fd5da86
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Literature.TYZThm35ReadingA
---

# Tian–Yuan–Zhang's Theorem 3.5(2) in reading A

*Theorem 3.5(2) in reading A* is the following assertion. For every natural number $d$ with
$d\equiv5\pmod8$ and $d$ squarefree, and every entire continuation $F$ of $L(C_d,s)$ whose order
of vanishing at $s=1$ is at least $2$, both genus sums are even:
$$T^{\rm Cl}_{5a}(d)=0\quad\text{and}\quad T^{\rm Cl}_{5b}(d)=0\quad\text{in }\mathbb Z/2.$$

This is a consequence of Theorem 3.5(2) of Tian, Yuan and Zhang for $n=d\equiv5\pmod8$, under one
reading of their genus sums, reading A: the decompositions of $n$ are the set partitions of its
primes, each counted once, with a trivial factor $d_1=1$ allowed. In that reading their two sums
are $T^{\rm Cl}_{5a}(n)$ and $T^{\rm Cl}_{5a}(n)+T^{\rm Cl}_{5b}(n)$, so their evenness is the
conclusion above. Only the case $\mathcal L(n)=0$ of their theorem is needed: they define the
invariant $\mathcal L(n)$ from $L(C_n,1)$ or $L'(C_n,1)$ and set it to $0$ exactly when the order
of vanishing at $s=1$ is at least $2$. Their printed hypothesis is a condition on their genus point
$P(n)$, followed by an "i.e." that restates it as the evenness of $2^{-\rho(n)}\mathcal L(n)$ and
is not proved in the paper. When $\mathcal L(n)=0$, the condition on $P(n)$ follows directly from
the first assertion of their Theorem 3.5 and their Lemma 3.18, so the "i.e." is not needed.

No refereed text found by the project's literature search, which AI agents carried out, states
reading A explicitly; the one statement found is in an unrefereed preprint (Smith). Their
introductory theorem with the same parity criteria (Theorem 1.2 of the arXiv version, Theorem 1.4
of the journal version) requires every factor to exceed $1$; read that way it is false in both
versions, with counterexamples $d=26565$ and $d=33117$, and it is not cited. Their proof of
Theorem 3.5(2) passes through their Proposition 3.4, whose proof is only a sketch in the arXiv
version; the journal's proof was not assessed on this point, and the comparison of the two
versions was made by AI agents, not checked by a human. Proposition N, a new argument written for
this project, reviewed twice by AI models and never by a human, derives reading A from unambiguous
results of the paper without Proposition 3.4; it is supporting evidence, not a hypothesis. Reading A
is a hypothesis, not proved here.

## Depends on

- [Entire continuations of the L-series of an elliptic curve](l-series-continuation.md)
- [The first genus sum $T^{\rm Cl}_{5a}$](genus-sum-5a.md)
- [The genus sum of class numbers](../../redei/class-number-genus-sum.md)

## Sources

- [Reading A of Tian-Yuan-Zhang](../../../sources/rank-locators.md#reading-a-of-tian-yuan-zhang)
- [Proposition N](../../../sources/rank-5b-locators.md#proposition-n)
