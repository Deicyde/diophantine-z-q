---
article_id: af_75a8968399f5180685929541
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine, ZInQ.Manuscript.RestrictedConverse, ZInQ.Manuscript.SelmerTwoPower.SelmerCorankOne, ZInQ.Manuscript.AnalyticRankOne
---

# Theorem 5.3: the restricted converse

For every positive squarefree $\ell\equiv11\pmod{12}$, the curve $E_\ell:y^2=x(x-\ell)(x+3\ell)$ satisfies
$$\operatorname{corank}_{\mathbb Z_2}\mathrm{Sel}_{2^\infty}(E_\ell/\mathbb Q)=1\quad\Longrightarrow\quad\operatorname{ord}_{s=1}L(E_\ell,s)=1.$$

Here $\mathrm{Sel}_{2^\infty}$ is the genuine $2$-primary Selmer group, defined over Galois cohomology, and
corank $1$ means that it is isomorphic to $\mathbb Q_2/\mathbb Z_2$ times a finite group. The order of
vanishing is that of an entire function that agrees with the L-series of $E_\ell$ on $\operatorname{Re}s>3/2$.

This is the manuscript's own theorem, proved in its Sections 7–9 and Appendices E–G; it is not a printed
result of the literature. `ZInQ.OneProof.frozenTarget` takes it as the hypothesis `hRC`.

## Depends on

None.

## Sources

- [Theorem 5.3](../../sources/manuscript.md#theorem-53)
- [Section 7](../../sources/manuscript.md#section-7)
