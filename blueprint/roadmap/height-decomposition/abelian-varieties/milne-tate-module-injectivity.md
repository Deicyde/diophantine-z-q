---
article_id: af_8c346f471c1d8c65360ceeef
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves87.milneThm125Pts
---

# Endomorphisms agreeing on l-power torsion are equal

Let $k$ be an algebraically closed field, $\mathcal A$ an abelian surface over $k$ with a ring
homomorphism $\iota:\mathcal O\to\operatorname{End}(\mathcal A)$, and $\ell$ a prime different from
the characteristic of $k$. If two endomorphisms of $\mathcal A$ agree on every point of
$\mathcal A(k)$ of $\ell$-power order, they are equal.

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
It follows from Milne's Theorem 12.5 by the printed parts only: if $f$ and $g$ agree on every
$\mathcal A_{\ell^n}(k)$, then $T_\ell(f-g)=0$ (Remark 8.4 describes $T_\ell\mathcal A$ as the limit
of the $\mathcal A_{\ell^n}(k)$); the map
$\mathbb Z_\ell\otimes\operatorname{End}(\mathcal A)\to\operatorname{End}(T_\ell\mathcal A)$ is
injective, so $1\otimes(f-g)=0$; and $\operatorname{End}(\mathcal A)$ is a free $\mathbb Z$-module,
so $f=g$. The difference is taken in the commutative group $\operatorname{End}(\mathcal A)$
(Corollary 2.4). The action of $\mathcal O$ plays no part. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Milne Thm 12.5](../../../sources/height-decomposition-locators.md#milne-thm-125)
