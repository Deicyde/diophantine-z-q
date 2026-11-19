---
article_id: af_1d3baf6e12425de888228aca
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves70.y3ToP1j
---

# The quotient map from Y₃ to the projective line

The *quotient statement for $Y_3$* is the following assertion. Let $\overline{\mathbb Q}$ be an
algebraic closure of $\mathbb Q$, and let $Y$ be a proper smooth curve over $\mathbb Q$ with a
$\overline{\mathbb Q}$-point and with, for every field $F\supseteq\mathbb Q$, a bijection between
$Y(F)$ and the isomorphism classes of QM abelian surfaces over $F$ with a level-$3$ structure; say
that a point *classifies* the surfaces in its class. Suppose that, for every homomorphism of fields
$F\to F'$, the image in $Y(F')$ of a point of $Y(F)$ classifies the base change to $F'$ of the
surfaces that the point classifies, with their actions of $\mathcal O$ and their level structures;
that there is a single family over $Y$, that is, a proper smooth morphism $\mathcal A\to Y$ of
relative dimension $2$ with, for each $a\in\mathcal O$, an endomorphism $\iota(a)$ of $\mathcal A$
over $Y$ and a section $\eta(a)$ of $\mathcal A\to Y$, no group law or other condition being
required, such that each field-valued point of $Y$ classifies the fibre of $\mathcal A$ at that
point with the restrictions of the $\iota(a)$ and $\eta(a)$; and that every such family over a
proper smooth curve $S$ over $\mathbb Q$ whose fibre at each field-valued point, with the
restrictions of the $\iota(a)$ and $\eta(a)$, is a QM abelian surface with level-$3$ structure has a
morphism $S\to Y$ over $\mathbb Q$ taking each field-valued point of $S$ to a point classifying its
fibre. Then there is a morphism $\pi:Y\to\mathbf P^1_{\mathbb Q}$ with the following four
properties, in which $y$ and $y'$ are $\overline{\mathbb Q}$-points of $Y$ classifying
$(A,\iota,\eta)$ and $(A',\iota',\eta')$, and $\pi(y)$ is the image of $y$ in
$\mathbf P^1(\overline{\mathbb Q})=\overline{\mathbb Q}\cup\{\infty\}$. First, $\pi(y)=\pi(y')$
exactly when $(A',\iota')$ is isomorphic to the twist $(A,\iota\circ\alpha)$ for some ring
automorphism $\alpha$ of $\mathcal O$. Second, $\pi(y)=0$ exactly when the ring
$\operatorname{End}_{\mathcal O}(A)$ of endomorphisms of $A$ commuting with $\iota(\mathcal O)$
contains an element $\phi$ with $\phi^2=-1$; $\pi(y)=\infty$ exactly when it contains an element
$\phi$ with $\phi^2-\phi+1=0$; and $\pi(y)=-16/27$ exactly when it contains an element $\phi$ with
$\phi^2=-6$. Third, $\pi$ maps $Y(\overline{\mathbb Q})$ onto $\mathbf P^1(\overline{\mathbb Q})$.
Fourth, every fibre of $\pi$ on $Y(\overline{\mathbb Q})$ is finite, with at most $324$ points.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. This is the manuscript's own claim. In the proof of its
Theorem 4.1 the manuscript shows that central finite ideles act trivially on $Y_3$ and concludes
that the whole curve, "with all its determinant components", admits an action of
$N/(\mathbb A_f^\times K_3)$, where $N$ is the finite-adelic normalizer of $\widehat{\mathcal O}$,
with quotient $\mathbf P^1_j$ and
$\deg(Y_3\to\mathbf P^1_j)\le4|(\mathcal O/3\mathcal O)^\times|\le324$; for the identification of
the normalizer quotient with $\mathbf P^1_j$, with branch values $0,\infty,-16/27$, it cites Baba
and Granath and Lin and Yang. No print states the result at level $3$. The statement is made for
every curve with these moduli properties and asserts nothing about the existence of such a curve;
nor does it assert the action, only the fibres of $\pi$. It reads the quotient on
$\overline{\mathbb Q}$-points as the classes of the underlying QM abelian surfaces up to twist; that
these classes are the orbits of $N$ is an argument made on the spot. It reads the branch values as
the project reads the table in §3.1 of Baba and Granath, a locator that is unverified: the points at
which $\operatorname{End}_{\mathcal O}(A)$ contains a root of $x^2+1$, of $x^2-x+1$ or of $x^2+6$,
that is, the CM points of discriminants $-4$, $-3$ and $-24$, are exactly the fibres over $0$,
$\infty$ and $-16/27$, respectively. The locator audit found in Baba and Granath's Theorem 2.1 and
Lemma 3.1 that the quotient of the Shimura curve of level $\widehat{\mathcal O}^\times$ by its
Atkin–Lehner involutions is $\mathbf P^1_{\mathbb Q}$; these results do not fix the numerical values
of the coordinate. The indices $4,6,2$ that the manuscript gives with the branch values are not part
of the statement, and the fibre bound is the degree bound read on points, since a finite morphism of
degree $d$ has at most $d$ points in each geometric fibre. A review of this statement is pending. It
is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Y3 to P1j](../../../sources/height-decomposition-locators.md#y3-to-p1j)
