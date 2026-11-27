---
article_id: af_8e3831f30bd24cc15d990643
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves82.egaIV_9_7_7_OL
---

# The locus of geometrically connected fibres

The *constructibility statement* is the following assertion. Let $L$ be a number field,
$S=\operatorname{Spec}\mathcal O_L$, and $f:X\to S$ a smooth, quasi-compact and quasi-separated
morphism of schemes. Let $E$ be the set of points $s\in S$ whose fibre
$X_s=X\times_S\operatorname{Spec}k(s)$ is geometrically connected, in the sense that
$X_s\otimes_{k(s)}F$ is empty or connected for every field extension $F$ of $k(s)$. Then $E$ is
locally constructible in $S$: every point of $S$ has an open neighbourhood $V$ such that $E\cap V$
belongs to the smallest family of subsets of $V$ that contains the retrocompact open subsets and is
stable under finite intersections and complements.

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
It is Théorème (9.7.7)(ii) of EGA IV for $S=\operatorname{Spec}\mathcal O_L$ and smooth morphisms,
which are of finite presentation when quasi-compact and quasi-separated (EGA IV (1.6.1)). EGA
defines geometric connectedness by the number of connected components over an algebraic closure, at
most one; its equivalence with the form above is printed in EGA IV (4.5.1)–(4.5.2) and is not a Lean
theorem. The proof uses the statement only to show that a stable Faltings height built from a Néron
model is a height of a semi-abelian model in the sense of Gaudron and Rémond. It is a hypothesis,
not proved here.

## Depends on

None.

## Sources

- [EGA IV 9.7.7](../../../sources/height-decomposition-locators.md#ega-iv-977)
