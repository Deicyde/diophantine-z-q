---
article_id: af_641a8042c2f47ab8c7f49abc
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.BaseZeroAssembly.boundary45_finite_of_construction, ZInQ.Manuscript.RC.BaseZeroAssembly.boundary45_finite
---

# (4.5): the retained boundary

Assume, at one finite stage at the base $h_0=1$ with moving prime $r$ (`SplitNormStage`): the split norm
relation (4.1) at $r$ (the field `hnorm` of the stage, PRINT: Cai–Chen–Liu); the five-term sequence (H8)
with the torsion bound (H2) (`InfResInput`, PRINT and GLUE); that the Kummer class of the trace of a point
is the cohomological transfer of its class (GLUE, on classes); the two local facts of the Selmer cone, that
its local degree-zero maps are onto and its degree-one maps inject on cycles (ELLIOT, asserted at this step
of the manuscript); and, as definitions, that a global cocycle of zero class is a coboundary (`hexact`),
that the Kummer maps over $H_r$ and over $M_\varnothing$ are related by restriction (`hκ`), and that the
global parts of the two cycles below represent the pushed constructed class (`hzcls`) and $\delta(P)$
(`hjcls`), with $\delta$ the global Kummer map.

Let $z(0)$ be the Selmer-cone cycle of the class constructed in Proposition 8.3 for $I=\varnothing$,
pushed to $K$, and $j(P)$ the Kummer cycle of the conductor-one point $P$. Then, with
$L=m_0C_\pi C_{\rm bad}2^{2e}$ the fixed multiplier of (H11) and $m=a_r-2$, there is a retained $v$ with
$$z(0)-L\,m\,j(P)=dv.\tag{4.5}$$

The manuscript states (4.5) at every stage $i$ and every $h$, with $m_i=a_{r_i}-2\chi_h(r_i)$; the Lean
theorem is the base case $h_0=1$, where $\chi_h$ is trivial, over abstract groups and cochain maps.

The reduction of Theorem 5.3 does not use this theorem: the field `PostLeaves.base_zero` of [the remaining
hypotheses](../remaining-hypotheses.md) supplies the inner-limit form of (4.5) at the base
(`InnerLimit45Base`, whose stage boundaries are ELLIOT), from which the limit statement used in
[Lemma 8.11](lemma-8-11-base-zero.md) is proved. Its stages are `SplitNormStage`s, so the split clause of
Cai–Chen–Liu at the base is asked inside the field, as `SplitNormStage.hnorm` of each stage (PRINT); the
stand-alone print is not an input of the reduction, and the clause constrains nothing, since the trivial
stage meets it. The docstrings record that this data exists exactly when the central cycle is
$L\,\kappa(P)$ for some additive $\kappa$ and some $L\ne0$ (`nonempty_innerLimit45Base_iff`): no
constraint when $P$ has infinite order, and a zero central cycle when $P$ is torsion.

**Proof sketch.** At the base the weighted point of the stage is the trace of $y_r$, which (4.1) makes
$(a_r-2)P$. The constructed class is the Kummer class of $L$ times the weighted point, so the global classes
of $z(0)$ and $Lm\,j(P)$ agree. Their difference is a global coboundary, and the two local facts lift it
to a coboundary $dv$ in the Selmer cone.

## Depends on

- [Section 8: actual classes, local conditions and central comparison](README.md)

## Sources

- [Section 8](../../../sources/manuscript.md#section-8)
