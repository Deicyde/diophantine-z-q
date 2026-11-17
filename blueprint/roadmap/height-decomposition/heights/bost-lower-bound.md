---
article_id: af_c8b49eabbe55128e11c3f65c
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves40.bostLowerBoundPrinted
---

# Bost's lower bound for the Faltings height

The *Bost statement* is the following assertion. For an abelian variety $A$ of dimension $g$ over a
number field, every stable Faltings height $h_F(A)$ of $A$ satisfies
$$h_F(A)+\tfrac g2\log\pi\;\ge\;-\tfrac g2\log(2\pi),$$
that is, $h_D(A)\ge-\frac g2\log(2\pi)$.

The stable height is built as the literature builds it: from the Néron model of $A$ over a number
field where $A$ has semistable reduction at every prime, the lattice of invariant differentials of
top degree on that model, and the metric $(i/2)^g\int_{A(\mathbb C)}\eta\wedge\overline\eta$ at each
complex embedding. The statement is about every real number that is a stable height in this sense;
it does not assert that one exists.

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
Gaudron and Rémond print it with a complete proof, in Deligne's normalization, as Corollary 8.4 of
their 2014 paper in *Commentarii Mathematici Helvetici*; Bost's lecture, the usual citation, has not
been read. The project's earlier form of the statement, over its own coordinate form of the height,
is proved here from this one and the [structure theorem of Chevalley](chevalley-structure-theorem.md).
It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Bost lower bound](../../../sources/height-decomposition-locators.md#bost-lower-bound)
