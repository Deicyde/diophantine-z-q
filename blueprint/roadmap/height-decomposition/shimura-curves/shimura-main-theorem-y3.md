---
article_id: af_f97d8970086eaa3ee8b63bb0
declaration: def
origin: cited
statement: formalized
lean: HDec.HSyn.OpenResearchLeaves67.deligneCanonicalModelY3EveryPrint
---

# Shimura's Main Theorem I on Y₃ in Deligne's form

The *Shimura–Deligne statement on $Y_3$* is the following assertion. Let $\mathfrak H$ be the upper
half-plane in $\mathfrak H^\pm=\mathbb C\setminus\mathbb R$, $\widehat{\mathcal O}^\times$ the group
of units of the closure $\widehat{\mathcal O}$ of $\mathcal O$ in $B\otimes\mathbb A_f$, and
$K_3=\{k\in\widehat{\mathcal O}^\times: k\equiv1\bmod 3\widehat{\mathcal O}\}$. Let $B$ act on
$\mathbb C^2$, and by Möbius transformations on $\mathfrak H^\pm$, through a fixed embedding
$B\to\mathrm M_2(\mathbb R)$, which identifies $B\otimes\mathbb R$ with $\mathrm M_2(\mathbb R)$,
and for $\tau\in\mathfrak H$ let $J_\tau\in\mathrm M_2(\mathbb R)$ be the matrix with
$J_\tau(\tau,1)^T=i(\tau,1)^T$. Let $Y$ be a proper smooth curve over $\mathbb Q$ with, for every
field $F\supseteq\mathbb Q$, a bijection between $Y(F)$ and the isomorphism classes of QM abelian
surfaces over $F$ with a level-$3$ structure (an $\mathcal O$-linear injection
$\mathcal O/3\mathcal O\to A(F)$); say that a point *classifies* the surfaces in its class. Suppose
that these bijections are compatible with extension of $F$; that each point classifies the fibre at
that point of a single abelian scheme $\mathcal A$ over $Y$ with a ring homomorphism
$\mathcal O\to\operatorname{End}_Y(\mathcal A)$ and an $\mathcal O$-linear map
$\mathcal O/3\mathcal O\to\mathcal A(Y)$ that is a bijection onto $\mathcal A_s[3]$ at every
geometric point $s$; and that every abelian scheme of this kind over a proper smooth curve $S$ over
$\mathbb Q$, whose fibres at field-valued points are QM abelian surfaces with level-$3$ structure,
has a morphism $S\to Y$ taking each field-valued point of $S$ to a point classifying its fibre. Then
there is a map $\Psi:\mathfrak H^\pm\times(B\otimes\mathbb A_f)^\times\to Y(\mathbb C)$ with four
properties. First, $\Psi$ is surjective, and $\Psi(z,g)=\Psi(z',g')$ exactly when $z'=\gamma z$ and
$g'=\gamma gk$ for some $\gamma\in B^\times$ and $k\in K_3$; so $\Psi$ identifies
$B^\times\backslash\bigl(\mathfrak H^\pm\times(B\otimes\mathbb A_f)^\times\bigr)/K_3$ with
$Y(\mathbb C)$. Second, for every $g$ the map $\tau\mapsto\Psi(\tau,g)$ is holomorphic on
$\mathfrak H$. Third, for $\tau\in\mathfrak H$ and $u\in\widehat{\mathcal O}^\times$ the point
$\Psi(\tau,u)$ classifies a QM abelian surface $(A,\iota)$ with a level-$3$ structure such that
$H_1(A(\mathbb C),\mathbb Z)$, the abelianized fundamental group of $A(\mathbb C)$ with $\mathcal O$
acting through $\iota$, is isomorphic to $\mathcal O$ with left multiplication by an isomorphism
whose real extension $B\otimes\mathbb R\to H_1(A(\mathbb C),\mathbb R)=\operatorname{Lie}A$ carries
right multiplication by $J_\tau$ to multiplication by $i$. Fourth, Shimura's reciprocity law holds
at the CM points of $\mathfrak H$ in the following form: there are a sign $\varepsilon=\pm1$ and a
choice, made once for all fields, between an embedding into $\mathbb C$ and its complex conjugate,
such that for every imaginary quadratic field $K$, embedding $\kappa:K\to\mathbb C$, embedding
$q:K\to B$ and point $z\in\mathfrak H$ with $q(a)(z,1)^T=\kappa'(a)(z,1)^T$ for all $a\in K$, where
$\kappa'$ is the chosen one of $\kappa$ and $\bar\kappa$, and for every
$\sigma\in\operatorname{Aut}(\mathbb C)$ and every idele $s$ of $K$ such that $\sigma$ acts on each
finite abelian extension of $\kappa(K)$ in $\mathbb C$ as the Artin symbol of $s$, one has
$\sigma(\Psi(z,g))=\Psi\bigl(z,\hat q(s)^{\varepsilon}g\bigr)$ for every $g$, where
$\hat q:\mathbb A_{K,f}\to B\otimes\mathbb A_f$ is the extension of $q$ to finite adeles, applied to
the finite part of $s$.

It is not printed in this form but follows from published theorems; reaching it from the print takes
further theorems, which are not proved here. It is Shimura's Main Theorem I in Deligne's adelic
form, at $B=\left(\frac{2,-3}{\mathbb Q}\right)$ and level $K_3$, stated for every curve with these
moduli properties; it asserts nothing about the existence of such a curve. It is weaker than the
print in three ways: it asks for a bijection from the double coset space that is holomorphic in
$\tau$ in place of a biholomorphism; it states the moduli clause only at the points $(\tau,u)$ with
$u\in\widehat{\mathcal O}^\times$, without the polarization or the level structure; and it states
the reciprocity law only at CM points of $\mathfrak H$, with its sign conventions left open.
Deligne's moduli problem is the polarized one; that $H_1(A(\mathbb C),\mathbb Z)$ carries exactly
one principal Riemann form of the type the project fixes is proved here, and Riemann's theorem turns
it into the polarization. The project's earlier form, on the upper half-plane, is proved equivalent
to it. It is a hypothesis, not proved here.

## Depends on

None.

## Sources

- [Shimura Main Theorem I in Deligne form](../../../sources/height-decomposition-locators.md#shimura-main-theorem-i-in-deligne-form)
