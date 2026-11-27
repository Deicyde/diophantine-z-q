---
article_id: af_c8b49eabbe55128e11c3f65c
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves82.gaudronRemondSec9LowerGR1Weak
---

# The lower bound for the Faltings height

The *lower bound statement* is the following assertion. Let $A$ be an abelian variety of dimension
$g$ over a number field $K$. Then every height $h_F(A)$ of a semi-abelian model of $A$, in Faltings'
normalization, satisfies $h_F(A)\ge-\tfrac32\,g$. Here such a height is a real number of the form
$$h_F(A)=\frac1{[L:\mathbb Q]}\Bigl(\log\#\bigl(\omega/\mathcal O_L\eta\bigr)-\frac12\sum_{\tau:L\to\mathbb C}\log\|\eta\|_\tau^2\Bigr),$$
where $L\supseteq K$ is a number field, $\mathcal A$ is a semi-abelian model of $A_L$ over
$\mathcal O_L$ (a smooth separated group scheme of finite type over $\mathcal O_L$, with an
isomorphism of group schemes from its generic fibre to $A_L$, whose fibre at every maximal ideal is
connected and an extension of an abelian variety by a torus, over the residue field and over its
algebraic closure), $\omega$ is the lattice of invariant differentials of top degree on $\mathcal A$
along its zero section, $\eta\in\omega$ is nonzero with $\omega/\mathcal O_L\eta$ finite, and
$\|\eta\|_\tau^2=2^{-g}\int_{A_\tau(\mathbb C)}|\eta\wedge\overline\eta|$, integrated over the
complex manifold $A_\tau(\mathbb C)$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. Here, unlike the general case, the one further step is
proved in Lean (`ZInQ.HeightModelM.gaudronRemondSec9LowerGR1Weak_of_GR1`): Gaudron and Rémond's
Corollaire 8.4 states $h(A)\ge-\frac g2\log(2\pi)$ for their height $h=h_F+\frac g2\log\pi$ of a
semi-abelian model, that is $h_F(A)\ge-\frac g2\log(2\pi^2)$, and since
$\frac12\log(2\pi^2)<\frac32$ this gives the statement, a weakening they make themselves on p. 352.
That step is still an argument, so the statement is not the printed form and the strict count does
not count it as published; the corollary itself over this height passed a three-lens AI reading, and
the project declined to carry it instead, as it is stronger (ruling of 2026-11-24). They print no
formula for the normalized Arakelov degree, and the standard one is used here. The model is not
required to be commutative; that it is, is proved in Lean, and so are the passage from stalks to
global sections and one identity of wedges in the Hodge line; what remains a reading is that the
stalk formula and the global sections used here are those of the sheaf of differentials, which
Mathlib does not yet have. With the constructibility statement of EGA IV (9.7.7), the statement
implies the same bound for the stable Faltings heights of this section, built from Néron models, and
this implication is proved in Lean; the converse is not proved here. It is a hypothesis, not proved
here.

## Depends on

None.

## Sources

- [Gaudron-Remond lower bound](../../../sources/height-decomposition-locators.md#gaudron-remond-lower-bound)
