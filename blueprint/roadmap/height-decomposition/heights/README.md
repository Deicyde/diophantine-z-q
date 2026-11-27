---
article_id: af_69c5c0d9102417c980cb9c28
---

# Faltings 1983 and Faltings heights

Let $K$ be a number field with absolute Galois group $G_K$, $A$ an abelian variety of dimension $g$
over $K$, and, for a prime $\ell$, $T_\ell A$ the $\ell$-adic Tate module of $A$ and
$V_\ell(A)=T_\ell A\otimes_{\mathbb Z_\ell}\mathbb Q_\ell$. For a number field $L\supseteq K$ and a
Néron model $\mathcal N$ of $A_L$ over $\mathcal O_L$, the $\mathcal O_L$-module $\omega$ of
invariant differentials of top degree on $\mathcal N$ carries at each embedding $\tau:L\to\mathbb C$
the metric $\|\eta\|_\tau^2=(i/2)^g\int_{A_\tau(\mathbb C)}\eta\wedge\overline\eta$; the *height* of
$\mathcal N$ is the Arakelov degree of $\omega$ with these metrics, divided by $[L:\mathbb Q]$. A
*stable Faltings height* of $A$ is the height of such a Néron model with semistable reduction at
every maximal ideal of $\mathcal O_L$: the identity component of each special fibre is an extension
of an abelian variety by a torus, over the residue field, over its algebraic closure or over both,
as each statement that uses it says. This is Faltings' normalization $h_F$; Deligne's is
$h_D=h_F+\frac g2\log\pi$. The height and semistable reduction enter through the project's own
definitions; that these agree with the published ones is a judgement of AI reviews. Two statements
below take instead the height of Gaudron and Rémond. For a number field $L\supseteq K$, a
*semi-abelian model* of $A_L$ is a smooth separated group scheme of finite type over $\mathcal O_L$,
with an isomorphism of group schemes from its generic fibre to $A_L$, whose fibre at every maximal
ideal is connected and an extension of an abelian variety by a torus, over the residue field and
over its algebraic closure; its height is built in the same way from its invariant differentials of
top degree along the zero section. By the constructibility statement of EGA IV (9.7.7) and a proof
in Lean, every stable Faltings height in the sense above is such a height; the converse is not
proved here.

Of these four statements, one is a published statement and three are consequences of published
theorems; none is proved here.

- [Pazuki's comparison of the theta height with the Faltings height](pazuki-bound.md)
- [Javanpeykar's bound for curves with a Belyi map](javanpeykar-bound.md)
- [The lower bound for the Faltings height](bost-lower-bound.md)
- [The isogeny theorem of Gaudron and Rémond](gaudron-remond-isogeny-bound.md)
