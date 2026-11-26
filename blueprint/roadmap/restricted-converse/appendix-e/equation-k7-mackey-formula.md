---
article_id: af_44677eb4d39b8933fd495f59
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.SelmerComplex.MackeyData.homologyMap_corCochains_comp_resCochains, ZInQ.Manuscript.RC.SelmerComplex.MackeyData.exists_of_finiteIndex, ZInQ.Manuscript.RC.SelmerComplex.res_cor_eq_zero_of_forall_conj
---

# (K7): the Mackey formula for restriction of a corestriction

Assume nothing: the Lean theorems take no named input.

Let $G$ be a topological group, $U\subseteq G$ an open subgroup of finite index, $V\subseteq G$ any
subgroup, and $M$ a topological $G$-module. Choose representatives $g$ of the double cosets
$V\backslash G/U$ with compatible transversals (such a choice always exists). Then on continuous
cohomology in every degree
$$\operatorname{res}^{G}_{V}\operatorname{cor}^{G}_{U}z
=\sum_{g\in V\backslash G/U}\operatorname{cor}^{V}_{V\cap gUg^{-1}}\,
\operatorname{res}^{gUg^{-1}}_{V\cap gUg^{-1}}(gz).\tag{K7}$$
In particular, if $\operatorname{res}^{gUg^{-1}}_{V\cap gUg^{-1}}(gz)=0$ for every $g\in G$, then
$\operatorname{res}^G_V\operatorname{cor}^G_Uz=0$.

The manuscript uses the formula for $G=G_K$, $U$ the absolute Galois group of a finite extension
$L/K$ and $V$ an inertia group, in degree one at each finite coefficient precision, to show that
the integral $j_*$ condition survives corestriction, also at ramified primes. The Lean statement is
the general identity, already an equality of cochain maps before passing to cohomology; the
application to Kato's classes is not formalized.

**Proof sketch.** With compatible right transversals, the corestriction cochain composed with
restriction to $V$ splits, term by term, into the sum over the double cosets; the identity holds on
inhomogeneous cochains and so on cohomology.

In the Lean proof of Theorem 5.3 this theorem is not used: the transfer argument lives inside the
step `AppEFromKato` described in [the overview](README.md).

## Depends on

None.

## Sources

- [Appendix E](../../../sources/manuscript.md#appendix-e)
