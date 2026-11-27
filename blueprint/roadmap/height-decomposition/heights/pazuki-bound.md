---
article_id: af_347612b60d11e0f53cbbd819
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves83.pazukiCor13Upper
---

# Pazuki's comparison of the theta height with the Faltings height

The *Pazuki statement* is the following assertion. Let $A$ be an abelian surface over a number field
$K$ and $h$ a stable Faltings height of $A$: the height of a Néron model $\mathcal N$ of $A_L$ over
$\mathcal O_L$, for some number field $L\supseteq K$, such that at every maximal ideal of
$\mathcal O_L$ the identity component of the fibre of $\mathcal N$ over an algebraic closure of the
residue field is an extension of an abelian variety by a torus. The height of $\mathcal N$ is the
Arakelov degree of its line of invariant differentials of top degree, with the metric
$\|\eta\|_\tau^2=(i/2)^2\int_{A_\tau(\mathbb C)}\eta\wedge\overline\eta$ at each embedding
$\tau:L\to\mathbb C$, divided by $[L:\mathbb Q]$. Let $\sigma:K\to\mathbb C$ be an embedding and
$\Lambda$ the kernel of a uniformization $\Phi:\mathbb C^2\to A_\sigma(\mathbb C)$: a surjective
homomorphism under which the preimage of the complex points of each Zariski open subset $U$ of $A$
is open and each regular function on $U$ is holomorphic along $\Phi$. Let $\Omega\in\mathfrak H_2$,
a symmetric complex $2\times2$ matrix with positive definite imaginary part, be a period matrix of
$\Lambda$: some $\mathbb C$-linear automorphism of $\mathbb C^2$ maps $\Lambda$ onto
$\Omega\mathbb Z^2+\mathbb Z^2$. For the sixteen characteristics $m=(\alpha,\beta)$ with
$\alpha,\beta\in\{0,\frac12\}^2$, let
$\theta_m(0,\Omega)=\sum_{n\in\mathbb Z^2}\exp\bigl(\pi i\,(n+\alpha)^{T}\Omega(n+\alpha)+2\pi i\,(n+\alpha)^{T}\beta\bigr)$.
Let $z=(z_m)$ have coordinates in a number field $F$ with an embedding $F\to\mathbb C$ that sends
$z_m$ to $c\,\theta_m(0,\Omega)$ for all $m$, for some $c\ne0$, and let $h_2(z)$ be its absolute
logarithmic height, with the $L^2$ norm at the archimedean places and the maximum norm at the finite
ones. Put $a=\max(1,h_2(z))$ and $b=\max(1,h+\log\pi)$. Then
$$a-\tfrac b2\le C_2\log\bigl(\min(a,b)+2\bigr),\qquad C_2=1000\cdot2^4(\log2^4)^5.$$

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. It is the upper half of the printed corollary. Reaching
it from the print takes reading an analytic principal polarization of $\mathbb C^2/\Lambda$ as an
algebraic one (Appell–Humbert and Lefschetz with GAGA, and the equality of the Néron–Severi groups
of $A$ over $\overline{\mathbb Q}$ and over $\mathbb C$), and showing that the uniformization is
biholomorphic. If the level-$2$ theta coordinates in Pazuki's paper are the second-order ones, this
statement is about $\log4$ stronger than the print, and whether the argument tolerates the weaker
constant has not been checked. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Pazuki bound](../../../sources/height-decomposition-locators.md#pazuki-bound)
