---
article_id: af_c8b49eabbe55128e11c3f65c
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves71.gaudronRemondSec9LowerAnSS
---

# The lower bound for the Faltings height

The *lower bound statement* is the following assertion. Let $A$ be an abelian variety of dimension
$g$ over a number field $K$. Then every stable Faltings height $h_F(A)$ of $A$, in Faltings'
normalization, satisfies $h_F(A)\ge-\tfrac32\,g$. Here a *stable Faltings height* of $A$ is a real
number of the form
$$h_F(A)=\frac1{[L:\mathbb Q]}\Bigl(\log\#\bigl(\omega/\mathcal O_L\eta\bigr)-\frac12\sum_{\tau:L\to\mathbb C}\log\|\eta\|_\tau^2\Bigr),$$
where $L\supseteq K$ is a number field, $\mathcal N$ is a Néron model of $A_L$ over $\mathcal O_L$
with semistable reduction at every maximal ideal of $\mathcal O_L$ (the identity component of the
special fibre is an extension of an abelian variety by a torus, both over the residue field and over
its algebraic closure), $\omega$ is the lattice of invariant differentials of top degree on
$\mathcal N$, $\eta\in\omega$ is nonzero with $\omega/\mathcal O_L\eta$ finite, and
$\|\eta\|_\tau^2=(i/2)^g\int_{A_\tau(\mathbb C)}\eta\wedge\overline\eta$, integrated over the
complex manifold $A_\tau(\mathbb C)$.

It is a published statement: the printed theorem, or a direct instance of it that needs no argument.
Its reading against the print or its review is not complete, and until both are the project's strict
count does not count it as published. Gaudron and Rémond use the inequality in the proof of their
Lemme 9.1, citing Bost through Corollary 8.4 of their 2014 paper in *Commentarii*; an AI reading of
both papers found the inequality in Faltings' original normalization, as here. That corollary states
$h(A)\ge-\frac g2\log(2\pi)$ for their height $h=h_F+\frac g2\log\pi$, which gives the stronger
$h_F(A)\ge-\frac g2\log(2\pi^2)$. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Bost lower bound](../../../sources/height-decomposition-locators.md#bost-lower-bound)
