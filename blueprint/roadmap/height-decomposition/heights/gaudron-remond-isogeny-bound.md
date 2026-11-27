---
article_id: af_7e432b9262db4dfd0cf66150
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves82.gaudronRemondThm14GR1
---

# The isogeny theorem of Gaudron and Rémond

The *isogeny statement* is the following assertion. Let $A$ and $B$ be abelian varieties over a
number field $K$ of degree $d$ that are isogenous over $K$, with $\dim A=g\geq1$, and let $h_F(A)$
be a height of a semi-abelian model of $A$, built as for the [lower bound](bost-lower-bound.md).
Then there are isogenies $A\to B$ and $B\to A$ over $K$ of degree at most
$$\kappa=\Bigl((14g)^{64g^2}\,d\,\max\bigl(h_F(A),\log d,1\bigr)^2\Bigr)^{1024g^3}.$$

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
Its reading against the print or its review is not complete, and until both are the project's strict
count does not count it as published. It is Theorem 1.4 of Gaudron and Rémond for isogenies over the
base field, with their stable height $h_F$ in Faltings' original normalization, which they take from
§2.3 of their paper in *Commentarii*; the printed couple of isogenies is split into two isogenies,
each of degree at most $\kappa$. It was read in Duke's typeset version of record, as posted on the
first author's page (its first-page footer gives the volume, issue and DOI, and its pages 2057–2108
match the journal's record), so the reading is against the journal text. Three steps of the height
that the reading took as arguments, the commutativity of the model, the passage from stalks to
global sections and one identity of wedges in the Hodge line, are now proved in Lean; what remains a
reading is that the stalk formula and the global sections used here are those of the sheaf of
differentials, which Mathlib does not yet have. The published rating still waits on the lead's
confirmation. With the constructibility statement of EGA IV (9.7.7), the statement implies the same
theorem for the stable Faltings heights of this section, built from Néron models, and this
implication is proved in Lean; the converse is not proved here. It is a hypothesis, not proved here.

## Depends on

- [The lower bound for the Faltings height](bost-lower-bound.md)

## Sources

- [Gaudron-Remond isogeny bound](../../../sources/height-decomposition-locators.md#gaudron-remond-isogeny-bound)
