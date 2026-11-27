---
article_id: af_36bc44a9d53a247992646d02
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves83.buzzardLemma22Full5
---

# An automorphism fixing a full level-5 structure is the identity

Let $k$ be an algebraically closed field whose characteristic is not $2$, $3$ or $5$, $\mathcal A$
an abelian surface over $k$ with an injective ring homomorphism
$\iota:\mathcal O\to\operatorname{End}(\mathcal A)$, and $\theta$ an automorphism of $\mathcal A$
commuting with $\iota(a)$ for every $a\in\mathcal O$. If $\theta$ fixes a point $P\in\mathcal A(k)$
such that $a\mapsto\iota(a)P$ is a bijection from $\mathcal O/5\mathcal O$ onto the $5$-torsion of
$\mathcal A(k)$, then $\theta$ is the identity.

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
Its reading against the print or its review is not complete, and until both are the project's strict
count does not count it as published. It is Buzzard's Lemma 2.2 at $N=5$, which is at least $4$ and
prime to $d=6$. The map $x\mapsto\iota(x)P$ is a full level-$5$ structure in his sense (Definition
1.1): $\mathcal A[5]$ is finite étale because $5$ is invertible (Milne, Proposition 20.7), hence
constant over $k$. Its orbit under Buzzard's group $H$ is a $V_1(5)$-structure, for any choice of
his $\kappa$, and an automorphism fixing $P$ fixes it. The order $\mathcal O$ meets Buzzard's
standing hypotheses: it is a maximal order (reduced discriminant $6$; Voight, Theorem 15.5.5) in the
indefinite quaternion algebra $(2,-3)_{\mathbb Q}$, which is ramified exactly at $2$ and $3$. It is
a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Buzzard Lemma 2.2 at N = 5](../../../sources/height-decomposition-locators.md#buzzard-lemma-22-at-n-5)
