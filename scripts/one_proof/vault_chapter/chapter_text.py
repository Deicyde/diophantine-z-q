"""Prose for blueprint/roadmap/height-decomposition/ (regenerated at each fold).

One entry per field of the H bundles. `gen.py` refuses to run when a field has no entry here, and
reports entries whose field is gone.
"""

GROUPS = [
    dict(dir='shimura-curves', title='Shimura curves of discriminant 6', intro=r"""
Let $B=\left(\frac{2,-3}{\mathbb Q}\right)$ be the quaternion algebra over $\mathbb Q$ with basis
$1,i,j,ij$, where $i^2=2$, $j^2=-3$ and $ij=-ji$; it has discriminant $6$, and
$\mathcal O=\mathbb Z+\mathbb Zi+\mathbb Z\frac{1+j}2+\mathbb Z\frac{i+ij}2$ is a maximal order. A
*QM abelian surface* over a field $F$ is an abelian surface $A$ over $F$ with an injective ring
homomorphism $\iota:\mathcal O\to\operatorname{End}_F(A)$; its *twist* by a ring automorphism $\alpha$
of $\mathcal O$ is $(A,\iota\circ\alpha)$. A *level-$3$ structure* on $(A,\iota)$ is an
$\mathcal O$-linear homomorphism $\eta:\mathcal O\to A(F)$ with kernel $3\mathcal O$, where
$\mathcal O$ acts on $A(F)$ through $\iota$. Isomorphisms are isomorphisms of abelian surfaces
compatible with $\iota$ and, when a level structure is part of the data, with $\eta$.

In the manuscript $Y_3$ is the Shimura curve of $B$ of level
$K_3=\ker\bigl(\widehat{\mathcal O}^\times\to(\mathcal O/3\mathcal O)^\times\bigr)$, where
$\widehat{\mathcal O}=\mathcal O\otimes\widehat{\mathbb Z}$, obtained as the generic fibre of a fine
moduli scheme over $\mathbb Z[1/30]$ for QM abelian surfaces with their canonical principal
polarization and a level-$3$ structure. A statement about $Y_3$ over $\mathbb Q$ is made for every
curve with the moduli properties that it lists, and asserts nothing about the existence of such a
curve; the lists differ from one statement to another. A *proper smooth curve* over a base is a
scheme over it that is proper and smooth of relative dimension $1$; it need not be connected.
"""),
    dict(dir='cm-fibres', title='Complex multiplication', intro=r"""
Let $k$ be an imaginary quadratic field, with ring of integers $\mathcal O_k$ and discriminant $d_k$. An *order* of $k$ is a subring $R$ of $\mathcal O_k$ of finite index $f=[\mathcal O_k:R]$, the conductor of $R$; its discriminant is $\Delta_R=f^2d_k$, and its class number is the order of its Picard group $\operatorname{Pic}(R)$, the group of isomorphism classes of invertible $R$-modules under the tensor product. An elliptic curve $E$ over a field $L$, an abelian variety of dimension $1$, has *complex multiplication by* $R$ when its ring of endomorphisms over an algebraic closure of $L$ is isomorphic to $R$.

Over a number field $L$, $E$ has *good reduction everywhere* when it is, as a group scheme, the generic fibre of an abelian scheme over $\mathcal O_L$: a smooth separated group scheme of finite type over $\mathcal O_L$ that is proper over $\mathcal O_L$. For an embedding $\sigma:L\to\mathbb C$, a *period* of $E$ at $\sigma$ is a complex number $\tau$ such that some surjective holomorphic homomorphism $\mathbb C\to E_\sigma(\mathbb C)$ has kernel $c(\mathbb Z+\tau\mathbb Z)$ for some $c\ne0$; on the upper half-plane, $\Delta(\tau)=(2\pi)^{12}\eta(\tau)^{24}$ is the modular discriminant, with Dedekind's $\eta(\tau)=e^{\pi i\tau/12}\prod_{n\ge1}(1-e^{2\pi in\tau})$. The manuscript's proof of its Theorem 4.1, the six-contact estimate, meets these curves at its CM fibres: abelian surfaces with quaternionic multiplication whose geometric endomorphism algebra is $\mathrm M_2(k)$ rather than the quaternion algebra, which the manuscript splits, up to isogeny, as the square of an elliptic curve with complex multiplication by an order of $k$.
"""),
    dict(dir='abelian-varieties', title='Abelian varieties', intro=r"""
Let $K$ be a field, $\overline K$ an algebraic closure of $K$ and $G_K=\operatorname{Aut}_K(\overline K)$;
let $A$ be an abelian variety over $K$, $A_{\overline K}=A\times_K\overline K$, and $\ell$ a prime
different from the characteristic of $K$. The Tate module $T_\ell A=\varprojlim_nA(\overline K)[\ell^n]$
is a $\mathbb Z_\ell$-module on which $G_K$ acts through its action on the points of $A$. The
$\ell$-adic cohomology of $A_{\overline K}$ is taken on the pro-étale site, with coefficients in the
sheaf of continuous $\mathbb Z_\ell$-valued functions, and $G_K$ acts on it through its action on
$\overline K$. The duality between the first cohomology group and the Tate module carries the
comparison theorems of $p$-adic Hodge theory, which are stated for cohomology, over to Tate modules.
"""),
    dict(dir='neron-models', title='Néron models, semistable reduction and monodromy', intro=r"""
Let $\mathcal O$ be a discrete valuation ring with fraction field $K$ and residue field $k$, and $A$
an abelian variety over $K$. A *Néron model* of $A$ over $\mathcal O$ is a smooth separated group
scheme of finite type over $\mathcal O$, with an isomorphism of group schemes from its generic fibre
to $A$, such that every morphism to $A$ from the generic fibre of a smooth $\mathcal O$-scheme
extends uniquely to a morphism into it; over a Dedekind domain the definition is the same. $A$ has
*semistable reduction* when the identity component of the special fibre of a Néron model is an
extension of an abelian variety by a torus. The condition is read in more than one way, over $k$ or
over an algebraic closure of $k$, with a split torus or with any torus, and a statement that uses it
says which reading it takes.

For an algebraic closure $\Omega$ of $K$ and a valuation ring $w$ of $\Omega$ over $\mathcal O$, the
*inertia group* of $w$ consists of the elements of $\operatorname{Gal}(\Omega/K)$ that map $w$ to
itself and act trivially on its residue field. For a prime $\ell$ invertible in $\mathcal O$,
$\operatorname{Gal}(\Omega/K)$ acts on the Tate module $T_\ell A=\varprojlim_nA(\Omega)[\ell^n]$.
"""),
    dict(dir='heights', title='Faltings 1983 and Faltings heights', intro=r"""
Let $K$ be a number field with absolute Galois group $G_K$, $A$ an abelian variety of dimension $g$
over $K$, and, for a prime $\ell$, $T_\ell A$ the $\ell$-adic Tate module of $A$ and
$V_\ell(A)=T_\ell A\otimes_{\mathbb Z_\ell}\mathbb Q_\ell$. For a number field $L\supseteq K$ and a
Néron model $\mathcal N$ of $A_L$ over $\mathcal O_L$, the $\mathcal O_L$-module $\omega$ of invariant
differentials of top degree on $\mathcal N$ carries at each embedding $\tau:L\to\mathbb C$ the metric
$\|\eta\|_\tau^2=(i/2)^g\int_{A_\tau(\mathbb C)}\eta\wedge\overline\eta$; the *height* of
$\mathcal N$ is the Arakelov degree of $\omega$ with these metrics, divided by $[L:\mathbb Q]$.

A *stable Faltings height* of $A$ is the height of such a Néron model with semistable reduction at
every maximal ideal of $\mathcal O_L$: the identity component of each special fibre is an extension
of an abelian variety by a torus, over the residue field, over its algebraic closure or over both,
as each statement that uses it says. This is Faltings' normalization $h_F$; Deligne's is
$h_D=h_F+\frac g2\log\pi$. The height and semistable reduction enter through the project's own
definitions; that these agree with the published ones is a judgement of AI reviews.
"""),
    dict(dir='p-adic-hodge', title='p-adic Hodge theory', intro=r"""
Let $p$ be a prime, $\overline{\mathbb Q}_p$ an algebraic closure of $\mathbb Q_p$, $\mathbb C_p$ its
completion, and $G_K=\operatorname{Gal}(\overline{\mathbb Q}_p/K)$ for a finite extension $K$ of
$\mathbb Q_p$ inside $\overline{\mathbb Q}_p$. Let $\chi_p$ be the cyclotomic character and
$\mathbb C_p(w)$ the space $\mathbb C_p$ on which $\sigma$ acts as $\chi_p(\sigma)^w\sigma$.
Hodge–Tate weights are read off these twists, and the literature gives $\chi_p$ the weight $1$ or
$-1$; a statement that uses Hodge–Tate weights says which convention it takes.

Let $A_{\rm inf}=W(\mathcal O_{\mathbb C_p}^\flat)$, with Fontaine's map
$\theta:A_{\rm inf}\to\mathcal O_{\mathbb C_p}$; $B_{\rm dR}^+$ is the completion of
$A_{\rm inf}[1/p]$ along $\ker\theta$, and $B_{\rm dR}$ is $B_{\rm dR}^+$ with the generators of
$\ker\theta$ inverted. A representation $V$ of $G_K$ on a finite-dimensional $\mathbb Q_p$-vector
space is *de Rham* when
$\dim_{\mathbb Q_p}(B_{\rm dR}\otimes_{\mathbb Q_p}V)^{G_K}=[K:\mathbb Q_p]\dim_{\mathbb Q_p}V$, and
*potentially semistable* when
$\dim_{B_{\rm st}^{G_{K'}}}(B_{\rm st}\otimes_{\mathbb Q_p}V)^{G_{K'}}=\dim_{\mathbb Q_p}V$ for some
finite extension $K'$ of $K$ inside $\overline{\mathbb Q}_p$, where $B_{\rm st}=B_{\rm cris}[\log[\tilde p]]$
is Fontaine's ring as Brinon and Conrad define it, taken inside $B_{\rm dR}$ with $\log_p(p)=0$.
"""),
    dict(dir='modular-galois', title='Galois representations of modular forms', intro=r"""
Cusp forms $f=\sum_{n\ge1}a_n(f)q^n$ of weight $k$ on $\Gamma_1(N)$ carry the Hecke operators $T_n$
and the diamond operators $\langle d\rangle$, $d\in(\mathbb Z/N)^\times$; $S_k(N,\chi)$ is the space of
those on which every $\langle d\rangle$ acts by $\chi(d)$, for a Dirichlet character $\chi$ modulo
$N$. A *normalized eigenform* is an element of some $S_k(N,\chi)$ that is an eigenvector of every
$T_n$ and has $a_1(f)=1$. A *newform* of level $N$ is a cusp form $f$ with $a_1(f)=1$ on which the
diamond operators act through a character and which is a Hecke eigenform new at level $N$ in the
sense of Atkin, Lehner and Li. The statements read this in one of two ways, which agree by the
theory of newforms: $f$ is an eigenvector of every $T_n$ and lies outside the span of the forms
coming from lower levels, or $f$ is an eigenvector of the $T_n$ with $n$ prime to $N$ and lies in the
new subspace. The *coefficient field* $K_f\subset\mathbb C$ is generated over $\mathbb Q$ by the
$a_n(f)$, and $K_{f,\lambda}$ is its completion at a finite place $\lambda$.

An *arithmetic Frobenius* at a prime $p$ is an element of
$G_{\mathbb Q}=\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$ that maps a place of
$\overline{\mathbb Q}$ above $p$ to itself and acts on its residue field as $x\mapsto x^p$; a
*geometric Frobenius* is the inverse of one. In weight $2$ the forms are studied on a Jacobian $J$ of
a model of $X_1(N)$ over $\mathbb Q$.
"""),
]

LEAVES = {
    'deligneCanonicalModelY3EveryPrint': dict(
        group='shimura-curves', slug='shimura-main-theorem-y3',
        title="Shimura's Main Theorem I on Y₃ in Deligne's form",
        anchor='Shimura Main Theorem I in Deligne form',
        statement=r"""
The *Shimura–Deligne statement on $Y_3$* is the following assertion. Let $\mathfrak H$ be the upper half-plane in $\mathfrak H^\pm=\mathbb C\setminus\mathbb R$, $\widehat{\mathcal O}^\times$ the group of units of the closure $\widehat{\mathcal O}$ of $\mathcal O$ in $B\otimes\mathbb A_f$, and $K_3=\{k\in\widehat{\mathcal O}^\times: k\equiv1\bmod 3\widehat{\mathcal O}\}$. Let $B$ act on $\mathbb C^2$, and by Möbius transformations on $\mathfrak H^\pm$, through a fixed embedding $B\to\mathrm M_2(\mathbb R)$, which identifies $B\otimes\mathbb R$ with $\mathrm M_2(\mathbb R)$, and for $\tau\in\mathfrak H$ let $J_\tau\in\mathrm M_2(\mathbb R)$ be the matrix with $J_\tau(\tau,1)^T=i(\tau,1)^T$. Let $Y$ be a proper smooth curve over $\mathbb Q$ with, for every field $F\supseteq\mathbb Q$, a bijection between $Y(F)$ and the isomorphism classes of QM abelian surfaces over $F$ with a level-$3$ structure (an $\mathcal O$-linear injection $\mathcal O/3\mathcal O\to A(F)$); say that a point *classifies* the surfaces in its class. Suppose that these bijections are compatible with extension of $F$; that each point classifies the fibre at that point of a single abelian scheme $\mathcal A$ over $Y$ with a ring homomorphism $\mathcal O\to\operatorname{End}_Y(\mathcal A)$ and an $\mathcal O$-linear map $\mathcal O/3\mathcal O\to\mathcal A(Y)$ that is a bijection onto $\mathcal A_s[3]$ at every geometric point $s$; and that every abelian scheme of this kind over a proper smooth curve $S$ over $\mathbb Q$, whose fibres at field-valued points are QM abelian surfaces with level-$3$ structure, has a morphism $S\to Y$ taking each field-valued point of $S$ to a point classifying its fibre. Then there is a map $\Psi:\mathfrak H^\pm\times(B\otimes\mathbb A_f)^\times\to Y(\mathbb C)$ with four properties. First, $\Psi$ is surjective, and $\Psi(z,g)=\Psi(z',g')$ exactly when $z'=\gamma z$ and $g'=\gamma gk$ for some $\gamma\in B^\times$ and $k\in K_3$; so $\Psi$ identifies $B^\times\backslash\bigl(\mathfrak H^\pm\times(B\otimes\mathbb A_f)^\times\bigr)/K_3$ with $Y(\mathbb C)$. Second, for every $g$ the map $\tau\mapsto\Psi(\tau,g)$ is holomorphic on $\mathfrak H$. Third, for $\tau\in\mathfrak H$ and $u\in\widehat{\mathcal O}^\times$ the point $\Psi(\tau,u)$ classifies a QM abelian surface $(A,\iota)$ with a level-$3$ structure such that $H_1(A(\mathbb C),\mathbb Z)$, the abelianized fundamental group of $A(\mathbb C)$ with $\mathcal O$ acting through $\iota$, is isomorphic to $\mathcal O$ with left multiplication by an isomorphism whose real extension $B\otimes\mathbb R\to H_1(A(\mathbb C),\mathbb R)=\operatorname{Lie}A$ carries right multiplication by $J_\tau$ to multiplication by $i$. Fourth, Shimura's reciprocity law holds at the CM points of $\mathfrak H$ in the following form: there are a sign $\varepsilon=\pm1$ and a choice, made once for all fields, between an embedding into $\mathbb C$ and its complex conjugate, such that for every imaginary quadratic field $K$, embedding $\kappa:K\to\mathbb C$, embedding $q:K\to B$ and point $z\in\mathfrak H$ with $q(a)(z,1)^T=\kappa'(a)(z,1)^T$ for all $a\in K$, where $\kappa'$ is the chosen one of $\kappa$ and $\bar\kappa$, and for every $\sigma\in\operatorname{Aut}(\mathbb C)$ and every idele $s$ of $K$ such that $\sigma$ acts on each finite abelian extension of $\kappa(K)$ in $\mathbb C$ as the Artin symbol of $s$, one has $\sigma(\Psi(z,g))=\Psi\bigl(z,\hat q(s)^{\varepsilon}g\bigr)$ for every $g$, where $\hat q:\mathbb A_{K,f}\to B\otimes\mathbb A_f$ is the extension of $q$ to finite adeles, applied to the finite part of $s$.
""",
        caveat=r"""
It is Shimura's Main Theorem I in Deligne's adelic form, at $B=\left(\frac{2,-3}{\mathbb Q}\right)$ and level $K_3$, stated for every curve with these moduli properties; it asserts nothing about the existence of such a curve. It is weaker than the print in three ways: it asks for a bijection from the double coset space that is holomorphic in $\tau$ in place of a biholomorphism; it states the moduli clause only at the points $(\tau,u)$ with $u\in\widehat{\mathcal O}^\times$, without the polarization or the level structure; and it states the reciprocity law only at CM points of $\mathfrak H$, with its sign conventions left open. Deligne's moduli problem is the polarized one; that $H_1(A(\mathbb C),\mathbb Z)$ carries exactly one principal Riemann form of the type the project fixes is proved here, and Riemann's theorem turns it into the polarization. The project's earlier form, on the upper half-plane, is proved equivalent to it.
""",
        src=r"""
G. Shimura, Ann. of Math. 85 (1967), Main Theorem I; P. Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971), §§4–5 (Corollaire 5.7, Exemple 5.8); J. Milne, *Introduction to Shimura varieties* (2005), §§5–8 and 12–14. Numbers unverified.
""",
    ),
    'y3FullThreeRepZ30': dict(
        group='shimura-curves', slug='y3-integral-model',
        title='The integral model of Y₃ over ℤ[1/30]',
        anchor='Y3 over Z[1/30]',
        statement=r"""
The *integral model statement* is the following assertion. Over a scheme $S$, consider abelian schemes $\mathcal A$ of relative dimension $2$ with a ring homomorphism $\mathcal O\to\operatorname{End}_S(\mathcal A)$ and a full $\mathcal O$-linear level-$3$ structure: an $\mathcal O$-linear homomorphism $\mathcal O/3\mathcal O\to\mathcal A(S)$ that is a bijection onto $\mathcal A_s[3]$ at every geometric point $s$ of $S$. There are a proper smooth curve $\mathcal Y$ over $\mathbb Z[1/30]$ and such an abelian scheme $\mathcal A$ over $\mathcal Y$ that is universal on locally noetherian schemes over $\mathbb Z[1/30]$: for every locally noetherian $\mathbb Z[1/30]$-scheme $S$ and every such $\mathcal A'$ over $S$ there is exactly one morphism $g:S\to\mathcal Y$ over $\mathbb Z[1/30]$ for which $\mathcal A'$ is isomorphic to $g^*\mathcal A$ compatibly with the actions of $\mathcal O$ and the level structures.
""",
        caveat=r"""
This is the manuscript's own claim, which it derives from Buzzard's Theorem 2.1 and Corollary 2.3 at the level $V_1(5)$ over $\mathbb Z[1/30]$, the finite étale sheaf of $\mathcal O$-linear isomorphisms $\mathcal O/3\mathcal O\cong A[3]$, the free action of $(\mathcal O/5\mathcal O)^\times$ and descent. No print states it at level $3$: Buzzard excludes level structure at the primes dividing the discriminant. The statement asks for a proper curve where the manuscript has a projective one, tests the universal property only on locally noetherian bases, and omits the polarization; the two forms of the moduli problem agree through the canonical principal polarization, an argument made on the spot and not proved here. That the generic fibre of $\mathcal Y$ represents the same problem over $\mathbb Q$, and so is the curve $Y_3$ of this chapter, is proved here.
""",
        src=r"""
The 11/5 manuscript (`diophantine_zq.tex`, lines 443–477), the construction of the integral model of $Y_3$; K. Buzzard, *Integral models of certain Shimura curves*, Duke Math. J. 87 (1997), Theorem 2.1 and Corollary 2.3, read in the author's preprint (Theorem 2.1, p. 5; Corollary 2.3, p. 7; the moduli problem, without a polarization, p. 2; the canonical principal polarization, p. 3). The journal pages are unverified.
""",
    ),
    'y3ToP1j': dict(
        group='shimura-curves', slug='y3-quotient-map',
        title='The quotient map from Y₃ to the projective line',
        anchor='Y3 to P1j',
        statement=r"""
The *quotient statement for $Y_3$* is the following assertion. Let $\overline{\mathbb Q}$ be an algebraic closure of $\mathbb Q$, and let $Y$ be a proper smooth curve over $\mathbb Q$ with a $\overline{\mathbb Q}$-point and with, for every field $F\supseteq\mathbb Q$, a bijection between $Y(F)$ and the isomorphism classes of QM abelian surfaces over $F$ with a level-$3$ structure; say that a point *classifies* the surfaces in its class. Suppose that, for every homomorphism of fields $F\to F'$, the image in $Y(F')$ of a point of $Y(F)$ classifies the base change to $F'$ of the surfaces that the point classifies, with their actions of $\mathcal O$ and their level structures; that there is a single family over $Y$, that is, a proper smooth morphism $\mathcal A\to Y$ of relative dimension $2$ with, for each $a\in\mathcal O$, an endomorphism $\iota(a)$ of $\mathcal A$ over $Y$ and a section $\eta(a)$ of $\mathcal A\to Y$, no group law or other condition being required, such that each field-valued point of $Y$ classifies the fibre of $\mathcal A$ at that point with the restrictions of the $\iota(a)$ and $\eta(a)$; and that every such family over a proper smooth curve $S$ over $\mathbb Q$ whose fibre at each field-valued point, with the restrictions of the $\iota(a)$ and $\eta(a)$, is a QM abelian surface with level-$3$ structure has a morphism $S\to Y$ over $\mathbb Q$ taking each field-valued point of $S$ to a point classifying its fibre. Then there is a morphism $\pi:Y\to\mathbf P^1_{\mathbb Q}$ with the following four properties, in which $y$ and $y'$ are $\overline{\mathbb Q}$-points of $Y$ classifying $(A,\iota,\eta)$ and $(A',\iota',\eta')$, and $\pi(y)$ is the image of $y$ in $\mathbf P^1(\overline{\mathbb Q})=\overline{\mathbb Q}\cup\{\infty\}$. First, $\pi(y)=\pi(y')$ exactly when $(A',\iota')$ is isomorphic to the twist $(A,\iota\circ\alpha)$ for some ring automorphism $\alpha$ of $\mathcal O$. Second, $\pi(y)=0$ exactly when the ring $\operatorname{End}_{\mathcal O}(A)$ of endomorphisms of $A$ commuting with $\iota(\mathcal O)$ contains an element $\phi$ with $\phi^2=-1$; $\pi(y)=\infty$ exactly when it contains an element $\phi$ with $\phi^2-\phi+1=0$; and $\pi(y)=-16/27$ exactly when it contains an element $\phi$ with $\phi^2=-6$. Third, $\pi$ maps $Y(\overline{\mathbb Q})$ onto $\mathbf P^1(\overline{\mathbb Q})$. Fourth, every fibre of $\pi$ on $Y(\overline{\mathbb Q})$ is finite, with at most $324$ points.
""",
        caveat=r"""
This is the manuscript's own claim. In the proof of its Theorem 4.1 the manuscript shows that central finite ideles act trivially on $Y_3$ and concludes that the whole curve, "with all its determinant components", admits an action of $N/(\mathbb A_f^\times K_3)$, where $N$ is the finite-adelic normalizer of $\widehat{\mathcal O}$, with quotient $\mathbf P^1_j$ and $\deg(Y_3\to\mathbf P^1_j)\le4|(\mathcal O/3\mathcal O)^\times|\le324$; for the identification of the normalizer quotient with $\mathbf P^1_j$, with branch values $0,\infty,-16/27$, it cites Baba and Granath and Lin and Yang. No print states the result at level $3$. The statement is made for every curve with these moduli properties and asserts nothing about the existence of such a curve; nor does it assert the action, only the fibres of $\pi$. It reads the quotient on $\overline{\mathbb Q}$-points as the classes of the underlying QM abelian surfaces up to twist; that these classes are the orbits of $N$ is an argument made on the spot. It reads the branch values as the project reads the table in §3.1 of Baba and Granath, a locator that is unverified: the points at which $\operatorname{End}_{\mathcal O}(A)$ contains a root of $x^2+1$, of $x^2-x+1$ or of $x^2+6$, that is, the CM points of discriminants $-4$, $-3$ and $-24$, are exactly the fibres over $0$, $\infty$ and $-16/27$, respectively. The locator audit found in Baba and Granath's Theorem 2.1 and Lemma 3.1 that the quotient of the Shimura curve of level $\widehat{\mathcal O}^\times$ by its Atkin–Lehner involutions is $\mathbf P^1_{\mathbb Q}$; these results do not fix the numerical values of the coordinate. The indices $4,6,2$ that the manuscript gives with the branch values are not part of the statement, and the fibre bound is the degree bound read on points, since a finite morphism of degree $d$ has at most $d$ points in each geometric fibre. A review of this statement is pending.
""",
        src=r"""
The 11/5 manuscript (`diophantine_zq.tex`, lines 420–440), in the proof of its Theorem 4.1: the normalizer quotient $\mathbf P^1_j$, with branch values $0,\infty,-16/27$ and indices $4,6,2$, cited to Baba–Granath and Lin–Yang (lines 420–422), and the action of $N/(\mathbb A_f^\times K_3)$ on $Y_3$ with the degree bound (lines 423–440). S. Baba and H. Granath, *Genus 2 curves with quaternionic multiplication*, Canad. J. Math. 60 (2008), Theorem 2.1, p. 737, and Lemma 3.1, pp. 739–740, read by the locator audit; the table of §3.1, p. 740, is unverified. The manuscript's bibliography cites the 2005 preprint of that paper (MPI für Mathematik), Sections 2.1 and 3 and Proposition 10, which was not located. Y.-H. Lin and Y. Yang, *Quaternionic loci in Siegel's modular threefold*, arXiv:1807.00466v1 (2018), the version the manuscript cites (journal version Math. Z. 295 (2020), 775–819, unverified); not read for this statement. The count $|(\mathcal O/3\mathcal O)^\times|=72$ is a computation of the project.
""",
    ),
    'cmHeight62': dict(
        group='cm-fibres', slug='elliptic-height-discriminant-formula',
        title='The discriminant formula for the Faltings height of an elliptic curve',
        anchor='Barquero-Sanchez et al. Eq. (6.2)',
        statement=r"""
The *discriminant formula statement* is the following assertion. Let $K$ be a number field, $L$ a number field containing $K$, and $E$ an elliptic curve over $K$ with good reduction everywhere over $L$: some smooth separated group scheme $\mathcal G$ of finite type over $\mathcal O_L$, proper over $\mathcal O_L$, has generic fibre isomorphic to $E_L$ as a group scheme. For each embedding $\sigma:L\to\mathbb C$ let $\tau_\sigma$ be a period of $E$ at $\sigma$, that is, at the restriction of $\sigma$ to $K$, with $\operatorname{Im}\tau_\sigma>0$: some surjective homomorphism $\Phi$ from $\mathbb C$ to the complex points $E_\sigma(\mathbb C)$ of $E$ through $\sigma$, under which the preimage of the complex points of each Zariski open subset $U$ of $E$ is open and each regular function on $U$ is holomorphic along $\Phi$, has kernel $c(\mathbb Z+\tau_\sigma\mathbb Z)$ for some $c\ne0$. Then
$$h_F(E)\le\frac1{[L:\mathbb Q]}\sum_{\sigma:L\to\mathbb C}-\frac1{12}\log\Bigl(\bigl|\Delta(\tau_\sigma)\bigr|\,(\operatorname{Im}\tau_\sigma)^6\Bigr),\qquad\Delta(\tau)=(2\pi)^{12}\eta(\tau)^{24}.$$
Here $h_F(E)$ is the stable Faltings height of $E$: the infimum in $[-\infty,+\infty]$, over all number fields $L'\supseteq K$ and all smooth separated group schemes $\mathcal N$ of finite type over $\mathcal O_{L'}$ whose generic fibre is isomorphic to $E_{L'}$ as a group scheme, of the height of $\mathcal N$, which is the Arakelov degree of the $\mathcal O_{L'}$-module $\omega_{\mathcal N}$ of invariant differentials of $\mathcal N$, with the metric $\|\omega\|_{\sigma'}^2=\frac i2\int_{E_{\sigma'}(\mathbb C)}\omega\wedge\overline\omega$ at each embedding $\sigma':L'\to\mathbb C$, divided by $[L':\mathbb Q]$.
""",
        caveat=r"""
Equation (6.2) of Barquero-Sanchez, Cadwallader, Cannon, Genao and Masri is the general formula for the Faltings height of an elliptic curve over a number field through its minimal discriminant and the modular discriminant at its periods, which the paper attributes to Silverman; the upstream review of the manuscript's CM argument read it in the published article, in Faltings' original metric and with $\Delta(\tau)=(2\pi)^{12}\eta(\tau)^{24}$. The statement is its case of good reduction everywhere, where the term of the minimal discriminant vanishes, and keeps only the inequality $\le$, the half the manuscript uses; it is not restricted to curves with complex multiplication. The manuscript's remark that the extension to $L$ does not change the stable height is built into the definition above, an infimum over all extensions. Reaching the statement from the print takes the comparison of the height in the paper with the height of $\mathcal G$ in that definition, which is not proved here. The display of (6.2) has not been re-read for this statement, and a review of the statement is pending.
""",
        src=r"""
A. Barquero-Sanchez, L. Cadwallader, O. Cannon, T. Genao and R. Masri, *Faltings heights of CM elliptic curves and special Gamma values*, Res. Number Theory 3 (2017), art. 13, §6, Eq. (6.2), pp. 13–14, with the metric on p. 1, read in the published article by the upstream review of the manuscript's CM argument (project note `docs/reviews/height-replacement/height/AUDIT.md`, item 2); the manuscript's citation (`diophantine_zq.tex`, lines 595–605). The paper attributes the formula to Silverman, Proposition 1.1 (not read).
""",
    ),
    'cmPotentialGood': dict(
        group='cm-fibres', slug='cm-potential-good-reduction',
        title='CM elliptic curves have potentially good reduction',
        anchor='CM potential good reduction',
        statement=r"""
The *potential good reduction statement* is the following assertion. Let $L$ be a number field and $E$ an elliptic curve over $L$ whose ring of endomorphisms over an algebraic closure of $L$ is isomorphic to an order of an imaginary quadratic field. Then there is a number field $L_1$ containing $L$ over which $E$ has good reduction everywhere: some smooth separated group scheme of finite type over $\mathcal O_{L_1}$, proper over $\mathcal O_{L_1}$, has generic fibre isomorphic to $E_{L_1}$ as a group scheme.
""",
        caveat=r"""
The manuscript uses the fact without a citation: "After a finite extension $E$ has everywhere good reduction, since its $j$-invariant is integral." It is classical. The $j$-invariant of an elliptic curve with complex multiplication is an algebraic integer, and an elliptic curve over a local field with integral $j$-invariant acquires good reduction over a finite extension (Silverman, Proposition VII.5.5); Serre and Tate prove that abelian varieties with complex multiplication have potentially good reduction everywhere, and Barquero-Sanchez, Cadwallader, Cannon, Genao and Masri prove it for elliptic curves with complex multiplication in the proof of their Theorem 1.3. The statement asks for one finite extension that gives good reduction at all finite places at once, in the form of an abelian scheme over its ring of integers; the passage from the local statements to this form is standard and is not proved here. The locators in Serre–Tate and Silverman are unverified, and a review of the statement is pending.
""",
        src=r"""
The 11/5 manuscript (`diophantine_zq.tex`, lines 596–597), without a citation. J.-P. Serre and J. Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968), 492–517 (locator unverified); J. H. Silverman, *The Arithmetic of Elliptic Curves*, Proposition VII.5.5 (number unverified); A. Barquero-Sanchez, L. Cadwallader, O. Cannon, T. Genao and R. Masri, *Faltings heights of CM elliptic curves and special Gamma values*, Res. Number Theory 3 (2017), art. 13, proof of Theorem 1.3, p. 15, read by the upstream review of the manuscript's CM argument (project note `docs/reviews/height-replacement/height/AUDIT.md`, item 2).
""",
    ),
    'cmjDegree': dict(
        group='cm-fibres', slug='cm-field-degree',
        title='The degree of a field of definition of a CM elliptic curve',
        anchor='Degree of singular moduli',
        statement=r"""
The *degree statement* is the following assertion. Let $L$ be a number field and $E$ an elliptic curve over $L$ whose ring of endomorphisms over an algebraic closure of $L$ is isomorphic to an order $R$ of an imaginary quadratic field. Then $\#\operatorname{Pic}(R)\le[L:\mathbb Q]$.
""",
        caveat=r"""
The manuscript uses the classical fact without a citation: "The degree of $j(E)$ is its order class number, so $h(\Delta)\le d\le D$." The classical theorem is that the $j$-invariant of an elliptic curve with complex multiplication by an order $R$ generates a field of degree $h(R)$ over $\mathbb Q$ (for orders, Cox's Theorem 11.1, through the ring class field of $R$); since $j(E)$ lies in $L$, the statement follows. Reaching it from the print also takes the identification of the class number of $R$ with $\#\operatorname{Pic}(R)$, which is standard and not proved here. The upstream audit of the manuscript's citations attributes the degree to §2.1 of Fowler's paper, which has not been read for this statement. Cox's theorem number is unverified, and a review of the statement is pending.
""",
        src=r"""
The 11/5 manuscript (`diophantine_zq.tex`, lines 585–587), without a citation. D. A. Cox, *Primes of the form $x^2+ny^2$*, Theorem 11.1 (number unverified). The upstream audit of the manuscript's citations (project note `docs/theorem-application-audit/FINDINGS.md`) attributes the degree and the integrality of the class polynomial of an order to G. Fowler, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, §2.1 (not read).
""",
    ),
    'fowlerProp27': dict(
        group='cm-fibres', slug='fowler-class-number-bound',
        title="Fowler's bound for discriminants of bounded class number",
        anchor='Fowler Proposition 2.7',
        statement=r"""
The *Fowler statement* is the following assertion. Let $k$ be an imaginary quadratic field, with ring of integers $\mathcal O_k$ and discriminant $d_k$, and $R$ an order of $k$, a subring of $\mathcal O_k$ of finite index $f=[\mathcal O_k:R]$; put $\Delta_R=f^2d_k$, and let $\operatorname{Pic}(R)$ be the Picard group of $R$, the group of isomorphism classes of invertible $R$-modules. Then for every integer $n\ge1$ with $\#\operatorname{Pic}(R)\le n$,
$$\sqrt{|\Delta_R|}\le2n^2\exp\bigl(21000\,n^2\bigr).$$
""",
        caveat=r"""
Fowler's Proposition 2.7 gives $\sqrt{|\Delta|}\le2n^2\exp(21000n^2)$ for every negative discriminant $\Delta$ of an imaginary quadratic order with class number $h(\Delta)\le n$, with no exceptional field; the manuscript cites it and applies it at $n=D$. The statement reads the print on orders, with $\Delta=\Delta_R=f^2d_k$ and $h(\Delta)=\#\operatorname{Pic}(R)$; both identifications are standard (Cox, Lemma 7.2 and Theorem 7.7) and are not proved here. The upstream review of the manuscript's CM argument read the proposition in the published article; the reading has not been repeated for this statement, and its review is pending.
""",
        src=r"""
G. Fowler, *Some uniform effective results on André–Oort for sums of powers in $\mathbb C^n$*, Math. Proc. Cambridge Philos. Soc. 180 (2026), 607–641, Proposition 2.7, printed pp. 615–616 (article pp. 9–10), read in the publisher's full text by the upstream review of the manuscript's CM argument (project note `docs/reviews/height-replacement/height/AUDIT.md`, item 1); the manuscript's citation (`diophantine_zq.tex`, lines 588–593). Discriminants and class numbers of orders: D. A. Cox, *Primes of the form $x^2+ny^2$*, Lemma 7.2 and Theorem 7.7 (numbers unverified).
""",
    ),
    't10TateDuality': dict(
        group='abelian-varieties', slug='tate-module-duality',
        title='The first ℓ-adic cohomology of an abelian variety is dual to its Tate module',
        anchor='Milne Theorem 12.1',
        statement=r"""
The *duality statement for the Tate module* is the following assertion. Let $K$ be a field, $\overline K$ an algebraic closure, $G_K=\operatorname{Aut}_K(\overline K)$, $A$ an abelian variety over $K$, $A_{\overline K}=A\times_K\overline K$, and $\ell$ a prime different from the characteristic of $K$. Let $H^1(A_{\overline K},\mathbb Z_\ell)$ be the first cohomology group of the pro-étale site of $A_{\overline K}$ with coefficients in the sheaf $U\mapsto C(U,\mathbb Z_\ell)$ of continuous $\mathbb Z_\ell$-valued functions, a $\mathbb Z_\ell$-module on which $\sigma\in G_K$ acts by pull-back along the automorphism $1\times\operatorname{Spec}\sigma$ of $A_{\overline K}$, and let $G_K$ act on the Tate module $T_\ell A=\varprojlim_n A(\overline K)[\ell^n]$ through its action on the points of $A$. Then there is an isomorphism of $\mathbb Z_\ell$-modules $\phi:H^1(A_{\overline K},\mathbb Z_\ell)\to\operatorname{Hom}_{\mathbb Z_\ell}(T_\ell A,\mathbb Z_\ell)$ with $\phi(\sigma x)=\phi(x)\circ\sigma^{-1}$ for every $\sigma\in G_K$ and every $x$.
""",
        caveat=r"""
Milne prints the isomorphism for an abelian variety over a separably closed field, with the étale cohomology group $H^1(A_{\rm et},\mathbb Z_\ell)$, as Theorem 12.1(a) with Remark 12.5, and records in that remark, without proof, that it is compatible with the natural action of $\operatorname{Gal}(k^{\rm sep}/k)$ when $A$ is defined over $k$; the statement applies this to $A_{\overline K}$. An AI reading of the notes found the statement a consequence of these, not a direct instance, through two steps: the agreement of pro-étale cohomology with coefficients $C(-,\mathbb Z_\ell)$ with étale $\ell$-adic cohomology, a comparison theorem of Bhatt and Scholze, and the use of an algebraic closure in place of a separable closure, which changes nothing in characteristic $0$ and in general follows from the topological invariance of étale cohomology.
""",
        src=r"""
J. S. Milne, *Abelian varieties*, course notes, version 2.0 (March 16, 2008), Part I, Theorem 12.1(a), p. 55, and Remark 12.5, p. 56, read in the author's PDF; this is the version the manuscript cites (`diophantine_zq.tex`, lines 10966–10970). The 1986 chapter *Abelian varieties* in G. Cornell and J. H. Silverman (eds.), *Arithmetic Geometry*, Theorem 15.1(a), is not read. Pro-étale cohomology and its comparison with étale cohomology: B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015), Definition 6.8.1 and §5.6; these two numbers are unverified.
""",
    ),
    'elliotWildInertiaTrivial': dict(
        group='neron-models', slug='wild-inertia-trivial',
        title='Wild inertia acts trivially under semistable reduction',
        anchor='Wild inertia on Tate modules',
        statement=r"""
The *wild inertia statement* is the following assertion. Let $K$ be a number field, $\mathcal O$ a
discrete valuation ring with fraction field $K$, $\Omega$ an algebraic closure of $K$, $w$ a
valuation ring of $\Omega$ over $\mathcal O$, and $\ell$ a prime invertible in $\mathcal O$. Let $A$
be an abelian variety over $K$ with semistable reduction at $\mathcal O$ in the sense of Silverberg
and Zarhin: some Néron model of $A$ over $\mathcal O$ has a special fibre over the residue field
whose identity component is an extension of an abelian variety by a torus, not necessarily split.
Then every element $\sigma$ of $\operatorname{Gal}(\Omega/K)$ in the inertia group of $w$ that is
wild, in the sense that $v_w(\sigma x-x)>v_w(x)$ for every nonzero $x\in\Omega$, where $v_w$ is the
valuation of $w$, acts trivially on $T_\ell A=\varprojlim_n A(\Omega)[\ell^n]$.
""",
        caveat=r"""
This is a sentence of the manuscript, which cites nothing for it. At a prime $p$, once Raynaud's
criterion gives semistable reduction over the local field $F$ obtained from the completion by
adjoining the $3$-torsion of $A$ (the $5$-torsion if $p=3$), the manuscript says: "Its wild inertia
acts trivially on each $V_\ell(A)$ with $\ell\ne p$." The statement reads this at a finite place of
a number field, through two standard identifications (the decomposition group of $w$ is the Galois
group of the completion, and Néron models commute with completion), and on $T_\ell A$, which embeds
in $V_\ell(A)$. It is true and standard: under semistable reduction inertia acts unipotently on
$T_\ell A$ (SGA 7 I, Exposé IX, Proposition 3.5), and wild inertia is pro-$p$, so it acts on each
$A(\Omega)[\ell^n]$ with period prime to $\ell$. An argument given here derives the statement from
these two facts, neither of which is proved here.
""",
        src=r"""
The 11/5 manuscript (`diophantine_zq.tex`, lines 817–818), without citation, right after its
citation of Silverberg and Zarhin's Theorem 3.5 (line 816). For the standard argument: SGA 7 I,
Exposé IX (A. Grothendieck), LNM 288 (1972), Proposition 3.5, p. 350, read in the MSRI/SLMath scan;
that wild inertia is pro-$p$, J.-P. Serre, *Corps locaux*, Chapter IV, §2 (numbers unverified).
""",
    ),
    'neronSchemeExtensionDedekind': dict(
        group='neron-models', slug='neron-models-exist',
        title='Néron models over Dedekind domains',
        anchor='Neron models exist',
        statement=r"""
The *Néron existence statement* is the following assertion. Let $D$ be a Dedekind domain that is not
a field, with fraction field $L$, and $A$ an abelian variety over $L$. Then there is a smooth,
separated, quasi-compact scheme $N$ over $D$ with generic fibre $A$ such that, for every smooth
$D$-scheme $Y$, every morphism $Y_L\to A$ extends to a morphism $Y\to N$.
""",
        caveat=r"""
It asks only for the existence of the extension, which is unique since $Y$ is flat over $D$ and $N$ is
separated, and it is stated over an affine base; the group structure of the Néron model is not asked
for.
""",
        src=r"""
S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models* (1990), §1.4, Theorem 3, with §1.2,
Definition 1, the existence half over an affine Dedekind base. Numbers unverified.
""",
    ),
    'silverbergZarhinThm35': dict(
        group='neron-models', slug='raynaud-criterion',
        title="Raynaud's criterion for semistable reduction",
        anchor='Raynaud criterion',
        statement=r"""
The *Raynaud statement* is the following assertion. Let $K$ be a field with a discrete valuation,
$n\ge3$ an integer not divisible by the residue characteristic, and $A$ an abelian variety over $K$
all of whose points of order dividing $n$ are defined over $K$. Then $A$ has semistable reduction:
for every Néron model of $A$, the identity component of its special fibre over the residue field is
an extension of an abelian variety by a torus, not necessarily split.
""",
        caveat=r"""
It is Theorem 3.5 of Silverberg and Zarhin, Raynaud's criterion, with the $n$-torsion defined over
$K$ where the print allows an extension unramified over the valuation. A reading of the page image
found the hypothesis $n\ge3$ (the text layer of the scan shows $n>3$).
""",
        src=r"""
A. Silverberg and Yu. G. Zarhin, *Semistable reduction and torsion subgroups of abelian varieties*,
Ann. Inst. Fourier 45 (1995), 403–420, Theorem 3.5, p. 406 (proof: SGA 7 I, IX, Proposition 4.7),
with semistable reduction as defined in §3, p. 405.
""",
    ),
    'faltingsLemma1DVRPrint': dict(
        group='heights', slug='faltings-extension-lemma',
        title='Homomorphisms of semiabelian schemes over a discrete valuation ring extend uniquely',
        anchor='Faltings 1983 Lemma 1',
        statement=r"""
The *extension statement for semiabelian schemes* is the following assertion. Let $K$ be a field,
$\mathcal O\subseteq K$ a valuation ring of $K$ that is a discrete valuation ring, with residue field
$k$, and $A$ and $B$ abelian varieties over $K$. Let $G$ and $H$ be smooth, separated, quasi-compact
group schemes over $\mathcal O$ with isomorphisms of group schemes $G_K\cong A$ and $H_K\cong B$ from
their generic fibres, and suppose that the special fibres $G_k$ and $H_k$ are connected and
semiabelian: each has an open connected subgroup scheme $U$ with a flat surjective homomorphism
$U\to C$ onto an abelian variety $C$ over $k$ whose kernel becomes isomorphic as a group scheme to
$\mathbb G_m^r$, for some $r\ge0$, after base change to an algebraic closure $\bar k$ of $k$; that is,
for every $\bar k$-algebra $R$ there is an isomorphism of groups from $(R^\times)^r$ onto the kernel of
$U(R)\to C(R)$, natural in $R$. Then for every homomorphism of group schemes $f:G_K\to H_K$ over $K$
there is exactly one morphism of $\mathcal O$-schemes $g:G\to H$ whose base change to $K$ is $f$.
""",
        caveat=r"""
Faltings states the lemma over any normal base $S$ with a dense open subscheme $U$, for a
homomorphism over $U$ between two semiabelian varieties over $S$: smooth algebraic groups whose
fibres are all connected of one common dimension $g$ and are extensions of an abelian variety by a
torus. The statement is the case of the spectrum of a discrete valuation ring and its generic point,
for models whose generic fibres are abelian varieties. Its hypotheses imply Faltings' definition.
The generic fibre is an abelian variety, hence connected and an extension of itself by the trivial
torus. A smooth model is flat, so its generic fibre is dense in it and the model is connected;
smoothness then makes the relative dimension constant on the model, so both fibres have the same
dimension. The project rates it a published statement in its printed form, a leaf: an AI reader read
p. 350 verbatim from the page image and found the statement a direct instance, an AI reviewer rated
it a leaf, and a third AI skeptic pass, checking fidelity to the print and the meaning of the formal
statement, could not refute it. It replaced the statement that the semistable height does not change
under extension of the base field, which is proved here from it, with Silverberg–Zarhin's criterion
and the existence of Néron models over a Dedekind base. The manuscript lists Faltings' paper and
cites it for other results, not for this lemma.
""",
        src=r"""
G. Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent. Math. 73 (1983),
349–366, §2, the Definition and Lemma 1, p. 350, read from the page image of the GDZ scan; the paper
is in the manuscript's bibliography (`diophantine_zq.tex`, lines 11084–11086) and cited at lines 621
and 733 for other results.
""",
    ),
    'gaudronRemondSec9LowerAnSS': dict(
        group='heights', slug='bost-lower-bound',
        title='The lower bound for the Faltings height',
        anchor='Bost lower bound',
        statement=r"""
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
""",
        caveat=r"""
Gaudron and Rémond use the inequality in the proof of their Lemme 9.1, citing Bost through Corollary 8.4
of their 2014 paper in *Commentarii*; an AI reading of both papers found the inequality in Faltings'
original normalization, as here. That corollary states $h(A)\ge-\frac g2\log(2\pi)$ for their height
$h=h_F+\frac g2\log\pi$, which gives the stronger $h_F(A)\ge-\frac g2\log(2\pi^2)$.
""",
        src=r"""
É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108, §9,
proof of Lemme 9.1, p. 2098, with the normalization of $h_F$ on p. 2058; the manuscript's citation.
É. Gaudron and G. Rémond, *Théorème des périodes et degrés minimaux d'isogénies*, Comment. Math.
Helv. 89 (2014), 343–403, Corollaire 8.4 and §2.3, as numbered in arXiv 1105.1230v1 (pp. 37 and 6–7),
which was read; the numbering of the published version is unverified. J.-B. Bost, Sém. Bourbaki 795,
Astérisque 237 (1996) (unread).
""",
    ),
    'gaudronRemondThm14AnSS': dict(
        group='heights', slug='gaudron-remond-isogeny-bound',
        title='The isogeny theorem of Gaudron and Rémond',
        anchor='Gaudron-Remond isogeny bound',
        statement=r"""
The *isogeny statement* is the following assertion. Let $A$ and $B$ be abelian varieties over a number
field $K$ of degree $d$ that are isogenous over $K$, with $\dim A=g$, and let $h_F(A)$ be a stable
Faltings height of $A$, built as for the [lower bound](bost-lower-bound.md). Then there are isogenies
$A\to B$ and $B\to A$ over $K$ of degree at most
$$\kappa=\Bigl((14g)^{64g^2}\,d\,\max\bigl(h_F(A),\log d,1\bigr)^2\Bigr)^{1024g^3}.$$
""",
        caveat=r"""
It is Theorem 1.4 of Gaudron and Rémond for isogenies over the base field, with the stable height in
Faltings' original normalization and semistable reduction in its printed form: the identity
component of the special fibre is semi-abelian over the residue field and over its algebraic
closure. A further reading of semistability, as the absence of $\mathbb G_a$ (SGA 7 IX 2.1.5), is
still to be matched.
""",
        src=r"""
É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108,
Théorème 1.4, p. 2060, with $\kappa$ on p. 2058.
""",
    ),
    'javanpeykarThm111An': dict(
        group='heights', slug='javanpeykar-bound',
        title="Javanpeykar's bound for curves with a Belyi map",
        anchor='Javanpeykar bound',
        statement=r"""
The *Javanpeykar statement* is the following assertion. Let $\overline{\mathbb Q}$ be an algebraic
closure of $\mathbb Q$ and $X$ an integral, projective, smooth proper geometrically connected curve
over $\overline{\mathbb Q}$ of genus $g=\dim H^1(X,\mathcal O_X)\ge1$ that has a Belyi map, a
finite morphism $X\to\mathbf P^1_{\overline{\mathbb Q}}$ unramified over
$\mathbf P^1\setminus\{0,1,\infty\}$; let $\deg_B(X)$ be the least degree of a Belyi map of $X$. Let
$W$ be an abelian variety over $\overline{\mathbb Q}$ that represents the degree-zero part of the
Picard functor of $X$, with the group law given by the tensor product of line bundles. Then every
stable Faltings height $h$ of $W$ satisfies $h\le13\cdot10^6\,g\,\deg_B(X)^5$; here a stable
Faltings height of $W$ is a stable Faltings height, built as for the
[lower bound](bost-lower-bound.md), of an abelian variety $V$ over a number field
$L\subset\overline{\mathbb Q}$ whose base change to $\overline{\mathbb Q}$ is isomorphic to $W$.
""",
        caveat=r"""
Javanpeykar's Theorem 1.1.1 bounds the Faltings height of the curve by its Belyi degree, and §2.3 of
his paper identifies that height with the stable Faltings height of the Jacobian; the statement is
the composite of the two, stated for the Jacobian. Semistability is that of the Néron model of the
Jacobian, not the semistability of a model of the curve that the paper uses. Reaching it from the
print also takes the fact that the height of a Néron model with semistable reduction everywhere does
not depend on the number field or on the model (Faltings 1983; Deligne, Sém. Bourbaki 616), so that
every stable height of $W$ in this sense is the stable Faltings height of the Jacobian.
""",
        src=r"""
A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8
(2014), Theorem 1.1.1, p. 90 (arXiv:1403.6404v1, p. 1), and §2.3, p. 98 (arXiv p. 9); the
manuscript's citation. AI-read: arXiv:1403.6404v1, pp. 1 and 9, and p. 90; p. 98 not checked.
Independence of the height: G. Faltings, Invent. Math. 73 (1983), 349–366; P. Deligne, Sém.
Bourbaki 616 (1983/84); locators unverified.
""",
    ),
    'pazukiCor13Upper': dict(
        group='heights', slug='pazuki-bound',
        title="Pazuki's comparison of the theta height with the Faltings height",
        anchor='Pazuki bound',
        statement=r"""
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
""",
        caveat=r"""
It is the upper half of the printed corollary. Reaching it from the print takes reading an analytic
principal polarization of $\mathbb C^2/\Lambda$ as an algebraic one (Appell–Humbert and Lefschetz with
GAGA, and the equality of the Néron–Severi groups of $A$ over $\overline{\mathbb Q}$ and over
$\mathbb C$), and showing that the uniformization is biholomorphic. If the level-$2$ theta coordinates
in Pazuki's paper are the second-order ones, this statement is about $\log4$ stronger than the print,
and whether the argument tolerates the weaker constant has not been checked.
""",
        src=r"""
F. Pazuki, *Theta height and Faltings height*, Bull. SMF 140 (2012), Corollary 1.3(2), upper half,
read by the locator audit. The level-$2$ coordinates are a risk (project note height-split, §8).
""",
    ),
    'r9a': dict(
        group='heights', slug='faltings-semisimplicity',
        title="Faltings' semisimplicity theorem",
        anchor='Faltings semisimplicity',
        statement=r"""
The *semisimplicity statement* is the following assertion. For an abelian variety $A$ over a number field $K$ and a prime $\ell$, the representation of $G_K$ on $V_\ell(A)$ is semisimple.
""",
        caveat=r"""

""",
        src=r"""
G. Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent. Math. 73 (1983), 349–366, §5, Satz 3, p. 360. Locator unverified.
""",
    ),
    'r9b': dict(
        group='heights', slug='faltings-tate-conjecture',
        title="Faltings' theorem on Tate's conjecture",
        anchor='Faltings Tate conjecture',
        statement=r"""
The *Tate statement* is the following assertion. For abelian varieties $A$ and $B$ over a number field $K$ and a prime $\ell$, the natural map $\operatorname{Hom}_K(A,B)\otimes\mathbb Z_\ell\to\operatorname{Hom}_{\mathbb Z_\ell}(T_\ell A,T_\ell B)$ is injective, with image the $G_K$-equivariant maps.
""",
        caveat=r"""

""",
        src=r"""
G. Faltings, Invent. Math. 73 (1983), §5, Satz 4 (the case $A=B$), p. 360, and Korollar 1 (Tate's conjecture), pp. 360–361. Locators unverified.
""",
    ),
    'bergerSurveyF': dict(
        group='p-adic-hodge', slug='berger-de-rham-potentially-semistable',
        title="Berger's theorem: de Rham representations are potentially semistable",
        anchor='Berger monodromy theorem',
        statement=r"""
The *Berger statement* is the following assertion. Let $E$ be a finite extension of $\mathbb Q_p$ inside $\overline{\mathbb Q}_p$ and $\rho:G_{\mathbb Q_p}\to\mathrm{GL}_n(E)$ a continuous representation, and let $V=E^n$, viewed as a representation of $G_{\mathbb Q_p}$ over $\mathbb Q_p$ of dimension $d=\dim_{\mathbb Q_p}V$. If $V$ is de Rham, that is, $\dim_{\mathbb Q_p}(B_{\rm dR}\otimes_{\mathbb Q_p}V)^{G_{\mathbb Q_p}}=d$, then $V$ is potentially semistable: there is a finite extension $K$ of $\mathbb Q_p$ inside $\overline{\mathbb Q}_p$ with $\dim_{B_{\rm st}^{G_K}}(B_{\rm st}\otimes_{\mathbb Q_p}V)^{G_K}=d$. Here $B_{\rm st}$ is the $\mathbb Q_p$-subalgebra of $B_{\rm dR}$ generated by $A_{\rm cris}$, $1/t$ and $\log[\tilde p]$: $A_{\rm cris}$ is the set of sums $\sum_{m\ge0}a_m\omega^m/m!$ in $B_{\rm dR}^+$ with $a_m\in A_{\rm inf}=W(\mathcal O_{\mathbb C_p}^\flat)$ tending to $0$ $p$-adically, where $\omega$ generates the kernel of $\theta:A_{\rm inf}\to\mathcal O_{\mathbb C_p}$; $t=\log[\varepsilon]$, where $\varepsilon=(1,\zeta_p,\zeta_{p^2},\dots)\in\mathcal O_{\mathbb C_p}^\flat$ is a compatible system of primitive $p$-power roots of unity; and $\log[\tilde p]=-\sum_{m\ge1}(1-[\tilde p]/p)^m/m$ for $\tilde p=(p,p^{1/p},\dots)$, Fontaine's $\log[\tilde p]$ with $\log_p(p)=0$. The assertion is made for every such $\omega$ and $\varepsilon$.
""",
        caveat=r"""
Brinon and Conrad state the theorem without proof, crediting Berger and André–Kedlaya–Mebkhout, as the "only if" half of their Theorem 9.3.5, with semistability defined by the equality of dimensions (§5.2). They construct $A_{\rm cris}$ and $B_{\rm st}$ abstractly and map them to $B_{\rm dR}$, while the statement uses the images: reaching it from their theorem takes their Theorem 9.2.10, that the map from $B_{\rm st}$ to $B_{\rm dR}$ is injective, and their description of the image of $A_{\rm cris}$ in $B_{\rm dR}^+$, for which they omit the proof that the map is injective; neither is proved here. Their de Rham condition is the one above because $B_{\rm dR}^{G_{\mathbb Q_p}}=\mathbb Q_p$, which is proved here. The statement takes the base field $\mathbb Q_p$ and representations of the form $E^n$. The manuscript cites Berger's paper, whose Théorème 0.6 is the same theorem over Berger's own variant of $B_{\rm st}$, which has the same $D_{\rm st}$.
""",
        src=r"""
O. Brinon and B. Conrad, *CMI summer school notes on $p$-adic Hodge theory* (preliminary version, June 24, 2009), Theorem 9.3.5, p. 148, the "only if" half; admissibility by dimension, §5.2, pp. 67–68; $A_{\rm cris}$, p. 128, and its image in $B_{\rm dR}^+$, p. 129; $B_{\rm cris}$, Definition 9.1.4, p. 131; $B_{\rm st}$, Definition 9.2.3, p. 138, its embedding in $B_{\rm dR}$, pp. 140–142, and Theorem 9.2.10, p. 143; $B_{\rm dR}^{G_K}=K$, Theorem 4.4.13, p. 64 (AI-read; in the manuscript's bibliography, which cites it for other results). The manuscript cites L. Berger, *Représentations $p$-adiques et équations différentielles*, Invent. Math. 148 (2002), 219–284, Théorème 0.6 = Théorème 5.19 (arXiv math/0102179v3, pp. 6 and 56, AI-read; Théorème 0.7 there is Sen's theorem); the journal numbering is unverified.
""",
    ),
    'conradAppB': dict(
        group='p-adic-hodge', slug='conrad-local-algebraicity',
        title='Local algebraicity of Hodge–Tate characters',
        anchor='Conrad Appendix B',
        statement=r"""
The *local algebraicity statement* is the following assertion. Let $E$ be a finite extension of $\mathbb Q_p$ inside $\overline{\mathbb Q}_p$ and $\psi:G_{\mathbb Q_p}\to E^\times$ a continuous character. Let $\chi$ be the $p$-adic cyclotomic character and $\mathrm{Art}:\mathbb Q_p^\times\to G_{\mathbb Q_p}^{\rm ab}$ the local Artin map, normalized so that uniformizers go to arithmetic Frobenius elements; thus $\chi(\mathrm{Art}(u))=u^{-1}$ for $u\in\mathbb Z_p^\times$. Call $\psi$ *locally algebraic of exponent* $m\in\mathbb Z$ if there is $k\ge0$ such that $\psi(\sigma)=u^m$ for every $u\in\mathbb Z_p^\times$ with $u\equiv1\pmod{p^k}$ and every $\sigma\in G_{\mathbb Q_p}$ whose image in $G_{\mathbb Q_p}^{\rm ab}$ is $\mathrm{Art}(u)$. For $i\in\mathbb Z$ let $H_i(\psi)$ be the $\mathbb Q_p$-vector space of $\mathbb Q_p$-linear maps $\phi:E\to\mathbb C_p$ with $\phi(\psi(\sigma)x)=\chi(\sigma)^i\,\sigma(\phi(x))$ for all $\sigma\in G_{\mathbb Q_p}$ and $x\in E$, and call the integer part of $\dim_{\mathbb Q_p}H_{-i}(\psi)/[E:\mathbb Q_p]$ the multiplicity of $i$ as a Hodge–Tate weight of $\psi$ (the cyclotomic character has weight $-1$). Then: (a) if some integer $w$ has multiplicity $1$ and every other integer has multiplicity $0$, then $\psi$ is locally algebraic of some exponent; (b) if $\psi$ is locally algebraic of exponent $-n$ for an integer $n$, then $\dim_{\mathbb Q_p}H_n(\psi)=[E:\mathbb Q_p]$.
""",
        caveat=r"""
Part (a) is the direction "Hodge–Tate implies locally algebraic" of the sentence after Conrad's Definition B.1, which he states for a finite extension $L$ of $\mathbb Q_p$ and credits to Tate through Serre's book, without proof; here $L=\mathbb Q_p$. Reaching (a) from it takes two steps not proved here: multiplicity $1$ for $w$ gives $\dim_{\mathbb Q_p}H_{-w}(\psi)\ge[E:\mathbb Q_p]$, which makes the underlying $\mathbb Q_p$-representation Hodge–Tate by the inequality $\sum_i\dim_{\mathbb Q_p}H_i(\psi)\le[E:\mathbb Q_p]$; and every homomorphism of tori $\mathbb G_m\to R_{E/\mathbb Q_p}\mathbb G_m$ over $\mathbb Q_p$ is $x\mapsto x^n$. Part (b) is Proposition B.3 at $L=\mathbb Q_p$, in Conrad's conventions: the arithmetic normalization, and the cyclotomic character of weight $+1$. Proposition B.3 assumes $\psi$ Hodge–Tate, which for a locally algebraic $\psi$ is the other direction of the same sentence; and passing from its conclusion, $\mathbb C_p\otimes_{\mathbb Q_p}E\cong\mathbb C_p(n)^{[E:\mathbb Q_p]}$, to $\dim_{\mathbb Q_p}H_n(\psi)=[E:\mathbb Q_p]$ takes linear algebra and the theorem of Ax, Sen and Tate, which is proved here, while the passage itself is not. Conrad's appendix is in an unrefereed author preprint, the version the manuscript cites; an AI reading of both pages found these statements there.
""",
        src=r"""
B. Conrad, *Lifting global representations with local properties*, author preprint, December 11, 2011, Appendix B: p. 32 (Definition B.1; the sentence after it, that $\psi$ is locally algebraic if and only if its underlying $\mathbb Q_p$-representation is Hodge–Tate, citing J.-P. Serre, *Abelian $\ell$-adic representations and elliptic curves*, III, A6, Corollary 2; the arithmetic normalization of the Artin map) and p. 33, Proposition B.3, with its proof on pp. 33–34 (AI-read); the manuscript's citation, Appendix B, pp. 32–33 (`diophantine_zq.tex`, lines 760–762). Serre's book is not read.
""",
    ),
    'panPrintedF': dict(
        group='p-adic-hodge', slug='pan-fontaine-mazur',
        title="Pan's Fontaine–Mazur theorem",
        anchor='Pan Theorem 1.0.4',
        statement=r"""
The *Fontaine–Mazur statement* is the following assertion. Let $p\ge5$ be a prime, $\iota_p:\overline{\mathbb Q}_p\to\mathbb C$ an isomorphism of fields, and $\rho:G_{\mathbb Q}\to\mathrm{GL}_2(\overline{\mathbb Q}_p)$ a continuous representation that is irreducible over $\overline{\mathbb Q}_p$, unramified outside finitely many primes and odd ($\det\rho(c)=-1$ for every complex conjugation $c$), and whose restriction to $G_{\mathbb Q_p}$ is potentially semistable in the sense of Fontaine and Hodge–Tate with two distinct Hodge–Tate weights. Then $\rho$ comes from a cuspidal eigenform up to twist: there are a nonzero cusp form $g$ of some weight on some $\Gamma_1(N)$, on which the diamond operators act through a character, that is an eigenvector of every Hecke operator $T_n$ with $n$ prime to $N$, with eigenvalues $\lambda_n(g)$; a continuous representation $\rho_g:G_{\mathbb Q}\to\mathrm{GL}_2(\overline{\mathbb Q}_p)$ attached to $g$ through $\iota_p$, in the sense that for all but finitely many primes $q\nmid N$ it is unramified at $q$ and every geometric Frobenius at $q$ has trace $\iota_p^{-1}(\lambda_q(g))$; a continuous character $\psi:G_{\mathbb Q}\to\overline{\mathbb Q}_p^\times$; and a matrix $P\in\mathrm{GL}_2(\overline{\mathbb Q}_p)$ with $\rho=\psi\cdot P\rho_gP^{-1}$. Each of the two local conditions is asked on some model $V=E^2$ of $\rho|_{G_{\mathbb Q_p}}$ over a finite extension $E$ of $\mathbb Q_p$ inside $\overline{\mathbb Q}_p$. *Hodge–Tate with two distinct weights* means that $\dim_E(V\otimes_{\mathbb Q_p}\mathbb C_p(w))^{G_{\mathbb Q_p}}$ is $1$ for two distinct integers $w$ and $0$ for every other $w$, where $\mathbb C_p(w)$ is $\mathbb C_p$ with $\sigma$ acting as $\chi_p(\sigma)^w\sigma$ for the cyclotomic character $\chi_p$, so that $\chi_p$ has Hodge–Tate weight $-1$. *Potentially semistable* means that for some finite extension $K$ of $\mathbb Q_p$ inside $\overline{\mathbb Q}_p$, $\dim_{B_{\rm st}^{G_K}}(B_{\rm st}\otimes_{\mathbb Q_p}V)^{G_K}=\dim_{\mathbb Q_p}V$, where $B_{\rm st}=B_{\rm cris}[\log[\tilde p]]$ is Fontaine's ring inside $B_{\rm dR}$, with $B_{\rm cris}=A_{\rm cris}[1/t]$ and $\log_p(p)=0$.
""",
        caveat=r"""
It is Theorem 1.0.4 of Pan, whose hypotheses are those of his Conjecture 1.0.1, taken for $p\ge5$; the print also covers $p=3$ under a further condition. A review checked every clause against the arXiv version that the manuscript cites, with Pan's conventions: geometric Frobenius, Hodge–Tate weight $-1$ for the cyclotomic character, and a fixed $\iota_p$. Potential semistability is Brinon and Conrad's notion, semistability over a finite extension with admissibility in the form of the equality of dimensions; that it does not depend on the model of $\rho$ is proved here, and so is the same for the Hodge–Tate condition. The review rates the statement a consequence because Brinon and Conrad define $B_{\rm st}$ abstractly: the statement uses its image in $B_{\rm dR}$, which is isomorphic to it by the injectivity in their Theorem 9.2.10, not proved here, and it uses their description of the image of $A_{\rm cris}$ in $B_{\rm dR}^+$, which they print without proof. The conclusion asks only for the traces at almost every prime, which is weaker than the printed modularity. Pan obtains Theorem 1.0.4 by combining his results with work of Skinner–Wiles, Kisin and Hu–Tan.
""",
        src=r"""
L. Pan, *The Fontaine–Mazur conjecture in the residually reducible case*, J. Amer. Math. Soc. 35 (2022), 1031–1169, Theorem 1.0.4, read in arXiv:1901.07166v2, the version the manuscript cites: Conjecture 1.0.1, p. 2; Theorem 1.0.4, p. 5; conventions (geometric Frobenius, Hodge–Tate weight $-1$ for the cyclotomic character), pp. 6–7. The journal numbering is unverified. Potential semistability in the sense of Fontaine as in O. Brinon and B. Conrad, *CMI summer school notes on $p$-adic Hodge theory* (preliminary version, June 24, 2009): admissibility in the dimension form, §5.2, pp. 67–68; $A_{\rm cris}$, p. 128, and its image in $B_{\rm dR}^+$, p. 129; $B_{\rm cris}$, Definition 9.1.4, p. 131; $B_{\rm st}$, Definition 9.2.3, p. 138, its embedding in $B_{\rm dR}$, pp. 140–142, injective by Theorem 9.2.10, p. 143; potential semistability, Theorem 9.3.5, p. 148.
""",
    ),
    'scholzeH1AbVar': dict(
        group='p-adic-hodge', slug='scholze-de-rham-comparison',
        title="Scholze's comparison theorem for H¹ of an abelian variety",
        anchor='Scholze comparison',
        statement=r"""
The *Scholze statement* is the following assertion. Let $F$ be a finite extension of $\mathbb Q_p$, $A$ an abelian variety of dimension $g$ over $F$, and $W=\mathbb Q_p\otimes_{\mathbb Z_p}H^1(A_{\overline F},\mathbb Z_p)$, where $H^1(A_{\overline F},\mathbb Z_p)$ is the first pro-étale cohomology group of $A_{\overline F}=A\times_F\overline F$ with coefficients in $\mathbb Z_p$, on which $G_F$ acts through its action on $\overline F$. Let $G_F$ act on $B_{\rm dR}$ through the restriction map $G_F\to G_{\mathbb Q_p}$ along an embedding of $\overline{\mathbb Q}_p$ in $\overline F$, put $D_{\rm dR}=(B_{\rm dR}\otimes_{\mathbb Q_p}W)^{G_F}$, and for $j\ge0$ let $\mathrm{Fil}^jD_{\rm dR}=D_{\rm dR}\cap(\mathfrak m^j\otimes_{\mathbb Q_p}W)$, where $\mathfrak m$ is the maximal ideal of $B_{\rm dR}^+$ and $\mathfrak m^0=B_{\rm dR}^+$. Then $W$ is finite-dimensional over $\mathbb Q_p$ and de Rham, that is, $\dim_{\mathbb Q_p}D_{\rm dR}=[F:\mathbb Q_p]\dim_{\mathbb Q_p}W$; the filtration has its jumps in $\{0,1\}$, that is, $\mathrm{Fil}^0D_{\rm dR}=D_{\rm dR}$ and $\mathrm{Fil}^2D_{\rm dR}=0$; and $\dim_{\mathbb Q_p}\mathrm{Fil}^1D_{\rm dR}=[F:\mathbb Q_p]\,g$.
""",
        caveat=r"""
Scholze's Corollary 1.8 is about a proper smooth rigid-analytic variety over a complete discretely valued extension of $\mathbb Q_p$ with perfect residue field: its étale cohomology with coefficients $\mathbb Q_p$ is de Rham, with associated filtered vector space its de Rham cohomology. The manuscript applies it to the analytification of $A$ and returns to algebraic cohomology through his Theorems 9.1 and 9.3. The statement is made on the étale side: under the filtered isomorphism $D_{\rm dR}\cong H^1_{\rm dR}(A/F)$ its last two clauses say that the Hodge filtration of $H^1_{\rm dR}(A/F)$ has its jumps in $\{0,1\}$ and that $\mathrm{Fil}^1H^1_{\rm dR}(A/F)=H^0(A,\Omega^1_A)$ has dimension $g$ over $F$. The manuscript's lemma is about abelian surfaces, whose Hodge numbers $2,2$ it states without a citation; the statement is for abelian varieties of every dimension. The cohomology here is pro-étale; its agreement with the classical $p$-adic étale cohomology, the inverse limit of the groups with coefficients $\mathbb Z/p^n$, is a further step not proved here.
""",
        src=r"""
P. Scholze, *$p$-adic Hodge theory for rigid-analytic varieties*, Forum Math. Pi 1 (2013), e1, Corollary 1.8, pp. 5–6, and Theorems 9.1 and 9.3, pp. 74–75 (arXiv:1205.3463v2, p. 4 and pp. 53–54), with the corrigendum, Forum Math. Pi 4 (2016), e6; read by the locator audit; the manuscript's citation. The 11/5 manuscript (`diophantine_zq.tex`): the lemma on de Rham comparison and finite descent, lines 10939–10965, and the Hodge numbers $2,2$, line 10996. For general $g$, $\dim_FH^0(A,\Omega^1_A)=g$: D. Mumford, *Abelian varieties*, §4; locator unverified.
""",
    ),
    'afCharpolyDS965': dict(
        group='modular-galois', slug='shimura-af-frobenius',
        title="Frobenius on the Tate module of Shimura's abelian variety",
        anchor='Diamond-Shurman 9.6.5 on Af',
        statement=r"""
The *Frobenius statement on $A_f$* is the following assertion. Let $f\in S_2(\Gamma_1(N))$ be a newform with character $\chi$, $N\ge2$; let $X$, $P_0$ and $J$ be as in the statement on [Hecke operators](hecke-operators-jacobian.md), $T_p$ ($p$ prime) and $\langle d\rangle$ ($d\in(\mathbb Z/N)^\times$) endomorphisms of $J$ over $\mathbb Q$ acting by the formulas there, and $I_f$ as in the statement on [Shimura's abelian variety](shimura-abelian-varieties.md). Let $A$ be an abelian variety over $\mathbb Q$ with a surjective homomorphism $\pi:J\to A$ that kills $I_fJ$ and through which every homomorphism from $J$ to an abelian variety killing $I_fJ$ factors uniquely, and let $\theta:K_f\to\operatorname{End}^0(A)$ be a ring homomorphism such that, for every prime $p$, $\theta(a_p(f))$ is an endomorphism $e$ of $A$ with $\pi\circ T_p=e\circ\pi$, and, for every $d$, $\chi(d)$ lies in $K_f$ and $\theta(\chi(d))$ is an endomorphism $e$ of $A$ with $\pi\circ\langle d\rangle=e\circ\pi$. Suppose that $K_f$ is a number field. Let $\ell$ be a prime, $\lambda$ a place of $K_f$ above $\ell$ and $V_\lambda=K_{f,\lambda}\otimes_{\mathbb Q_\ell\otimes K_f}V_\ell(A)$, where $K_f$ acts on $V_\ell(A)$ through $\theta$, and suppose that $V_\lambda$ is finite-dimensional over $K_{f,\lambda}$. Then for every prime $p\nmid N\ell$, $\chi(p)$ lies in $K_f$ and every arithmetic Frobenius at $p$ acts on $V_\lambda$ with characteristic polynomial $x^2-a_p(f)x+\chi(p)\,p$ over $K_{f,\lambda}$.
""",
        caveat=r"""
Diamond and Shurman's Theorem 9.6.5 asserts that there is a representation $\rho_{f,\lambda}$ in which Frobenius has this characteristic polynomial, and a paragraph after it, on the same page, identifies $\rho_{f,\lambda}$ for $k=2$ with the construction of their Section 9.5 on $V_\ell(A_f)$, which is $V_\lambda$. The statement asks for the polynomial on every $(A,\pi,\theta)$ with these properties of $A_f$, for newforms with $N\ge2$, and drops irreducibility and unramifiedness; that $K_f$ is a number field and that $V_\lambda$ is finite-dimensional are the print's presuppositions. A review rates it a consequence: the theorem is an existence statement, identified with $V_\lambda$ only in the text after it, and that the given Hecke operators and $I_f$ are Diamond and Shurman's rests on statements about the complex points and the Abel–Jacobi map of $X_1(N)$ that are not proved here. That $(A,\pi)$ is unique up to unique isomorphism, and $\theta$ determined by it, is proved here. Only AI agents have read the theorem and the paragraph after it, in the 2005 and 2016 printings.
""",
        src=r"""
F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228 (2005), Theorem 9.6.5 and the paragraph after it, p. 393 (fourth printing, 2016: p. 404); Lemma 9.5.3, Theorem 9.5.4 and Exercise 9.5.2(a), pp. 389–391; $A_f$ and the action of $K_f$, Definition 6.6.3, p. 241, and Proposition 6.6.4, p. 242 (all AI-read).
""",
    ),
    'bShStandardModel': dict(
        group='modular-galois', slug='hecke-operators-jacobian',
        title='Hecke operators on J₁(N) over ℚ',
        anchor='Hecke operators on J1(N)',
        statement=r"""
The *Hecke statement* is the following assertion. Let $N\ge2$ and let $X$ be a proper smooth geometrically connected integral curve over $\mathbb Q$ whose function field is generated by two functions $j_X,t_X$ with exactly the polynomial relations over $\mathbb Z$ of $j(\tau)$ and the Weber function $f_1(\tau)=\frac{g_2(\tau)g_3(\tau)}{\Delta(\tau)}\wp_\tau(1/N)$ on the upper half-plane, $\wp_\tau$ being the Weierstrass function of $\mathbb Z+\mathbb Z\tau$; such a curve is a model of $X_1(N)$ over $\mathbb Q$. Write $x_\tau$ for a point of $X(\mathbb C)$ at $\tau$, that is, a point at which every rational function of $j_X,t_X$ whose counterpart in $j,f_1$ has a limit at $\tau$ is regular with that value. Let $P_0$ be a rational point of $X$ and $J$ a Jacobian of $X$ with its Abel–Jacobi map based at $P_0$. Then there are endomorphisms $T_p$ ($p$ prime) and $\langle d\rangle$ ($d\in(\mathbb Z/N)^\times$) of $J$ over $\mathbb Q$ that act on the classes of degree-zero divisors supported on such points by
$$T_p[x_\tau]=\sum_{i<p}[x_{(\tau+i)/p}]+[x_{g(p\tau)}],\qquad\langle d\rangle[x_\tau]=[x_{g\tau}],$$
for every choice of these points, where the last term of $T_p$ occurs only for $p\nmid N$, and $g$ is any element of $\mathrm{SL}_2(\mathbb Z)$ with lower row $(c,d')$, $N\mid c$ and $d'\equiv p$, respectively $d'\equiv d$, modulo $N$.
""",
        caveat=r"""
Shimura's 1973 paper works on his standard model of $X_1(N)$ over $\mathbb Q$, which it defines by citing his 1971 book, with the Hecke correspondences $\xi_n$ acting on the Jacobian, and states, in the proof of its Theorem 1, that the elements of its Hecke ring lying in $\operatorname{End}(J)$ are rational over $\mathbb Q$; that a correspondence rational over $\mathbb Q$ induces an endomorphism of the Jacobian over $\mathbb Q$ is standard. Two steps are made on the spot and are not printed there: that a curve with these coordinates is Shimura's standard model, with the same points $x_\tau$, and that $\xi_p$ and $\langle d\rangle$ act on these points by Diamond and Shurman's double-coset formulas above, a matter of conventions. The pages read do not name the diamond operators; they lie in the Hecke ring tensored with $\mathbb Q$, and so are rational over $\mathbb Q$, by the Hecke relation $p\langle p\rangle=\xi_p^2-\xi_{p^2}$ for $p\nmid N$ and Dirichlet's theorem. The statement asserts the operators on every model with these coordinates. A review of this statement is pending.
""",
        src=r"""
G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc. Japan 25 (1973), 523–544: the Hecke operators $\xi_n$, p. 525; the standard model over $\mathbb Q$, by citation of his 1971 book, §7.3, and the rationality of the Hecke ring over $\mathbb Q$, p. 526 (AI page read). G. Shimura, *Introduction to the Arithmetic Theory of Automorphic Functions* (1971), §§7.2–7.3 (unread). The double-coset formulas: F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228 (2005), §6.3, pp. 226–227, Proposition 5.2.1, p. 171, and §7.9, p. 300 (AI-read).
""",
    ),
    'carayolThmAFrob': dict(
        group='modular-galois', slug='carayol-conductor',
        title="Carayol's theorem on the conductor",
        anchor='Carayol conductor',
        statement=r"""
The *Carayol statement* is the following assertion. Let $f$ be a newform of weight $2$, level $N$ and character $\psi$, whose coefficient field $K_f$ is a number field, and $\lambda$ a place of $K_f$ above a prime $\ell$. Then there is a continuous representation $\rho:G_{\mathbb Q}\to\mathrm{GL}_2(K_{f,\lambda})$ on $V=K_{f,\lambda}^2$ that is irreducible over $K_{f,\lambda}$; at every prime $p\nmid N\ell$ it is unramified, and every arithmetic Frobenius at $p$ has trace $a_p(f)$ and determinant $p\,\psi(p)$, so characteristic polynomial $X^2-a_p(f)X+p\,\psi(p)$; and at every prime $p\ne\ell$ the conductor exponent of its restriction to a decomposition group, $\operatorname{codim}V^{I_p}+\int_0^\infty\operatorname{codim}V^{G_p^u}\,du$ in the upper numbering, equals $v_p(N)$.
""",
        caveat=r"""
Darmon, Diamond and Taylor print the package as Theorem 3.1 (a)–(d) of their survey of Fermat's
Last Theorem, with absolute irreducibility; an AI reading found every clause printed there, the
conductor as clause (d). The Frobenius clause is in the normalization that the manuscript reads off
Carayol's theorem, and oddness is proved here from the determinant. Carayol's own statement,
compatibility with the local Langlands correspondence, has no Lean form; his §0.8 states the
conductor only for newforms with rational coefficients on $\Gamma_0(N)$.
""",
        src=r"""
H. Darmon, F. Diamond and R. Taylor, *Fermat's Last Theorem*, Current Developments in Mathematics 1995 (1997), Theorem 3.1 (a)–(d), pp. 85–86, and the conductor in §2, p. 54 (read in Darmon's copy); H. Carayol, Ann. Sci. ÉNS (4) 19 (1986), 409–468, Théorème (A), pp. 409–411, the manuscript's citation, with §0.8, p. 411 (read in the numdam copy); W. Casselman, Math. Ann. 201 (1973), Theorem 1; K. Ribet, LNM 601 (1977), Theorem 2.3. The numbers of Casselman's and Ribet's theorems are unverified.
""",
    ),
    'dsThm965Printed': dict(
        group='modular-galois', slug='deligne-representations',
        title="Deligne's Galois representations of eigenforms",
        anchor='Deligne representations',
        statement=r"""
The *Deligne statement* is the following assertion. Let $f\in S_k(N,\chi)$ be a normalized eigenform of
weight $k\ge2$ whose coefficient field $K_f$ is a number field, and $\lambda$ a prime of $K_f$ above a
prime $\ell$, with completion $K_{f,\lambda}$. Then there is a continuous representation
$\rho:G_{\mathbb Q}\to\mathrm{GL}_2(K_{f,\lambda})$ such that for every prime $p\nmid N\ell$: $\rho$ is
unramified at $p$, and for every arithmetic Frobenius $\sigma$ at $p$ either the characteristic
polynomial of $\rho(\sigma)$ is $x^2-a_p(f)x+\chi(p)p^{k-1}$ or $\rho(\sigma)$ satisfies this
polynomial.
""",
        caveat=r"""
Diamond and Shurman's theorem prints the characteristic polynomial ("the characteristic equation", in an AI reading of the 2005 and 2016 printings), which gives the statement directly; the alternative "satisfies" only weakens it. The statement drops the irreducibility of $\rho$, which the theorem also asserts, and assumes that $K_f$ is a number field, which the theorem presupposes.
""",
        src=r"""
F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228 (2005), Theorem 9.6.5, p. 393 (fourth printing, 2016: p. 404; AI-read), stated over $K_{f,\lambda}$, with their Definition 5.8.1 of normalized eigenforms; P. Deligne, Sém. Bourbaki 355 (1969); G. Shimura 1971, Theorem 7.14, for $k=2$. The numbers of Definition 5.8.1 and of Shimura's theorem are unverified.
""",
    ),
    'dsThm966Printed': dict(
        group='modular-galois', slug='deligne-serre',
        title='The Deligne–Serre theorem',
        anchor='Deligne-Serre',
        statement=r"""
The *Deligne–Serre statement* is the following assertion. Let $N\ge1$, let $\varepsilon$ be a Dirichlet character modulo $N$ with $\varepsilon(-1)=-1$, and let $f$ be a nonzero cusp form of weight $1$ on $\Gamma_1(N)$ on which every diamond operator $\langle d\rangle$ acts by $\varepsilon(d)$ and which is an eigenvector of every Hecke operator $T_n$ with $n$ prime to $N$, with eigenvalue $\lambda_n$. Then there is a continuous representation $\rho:G_{\mathbb Q}\to\mathrm{GL}_2(\mathbb C)$ with finite image, unramified at every prime $p\nmid N$, such that every arithmetic Frobenius at such a prime $p$ has trace $\lambda_p$ and determinant $\varepsilon(p)$.
""",
        caveat=r"""
It is Theorem 4.1 of Deligne and Serre with their hypotheses: a nonzero form of type $(1,\varepsilon)$ with $\varepsilon(-1)=-1$ that is an eigenvector of the Hecke operators away from the level, with no normalization of its coefficients; the statement takes the cusp forms among their modular forms. The condition $\varepsilon(-1)=-1$, which every nonzero form of weight $1$ and character $\varepsilon$ satisfies, is kept as in the print. The project's earlier form, for normalized eigenforms with trace $a_p(f)$, is proved here from this one. Only AI agents have read it against the paper, which is not in the manuscript's bibliography.
""",
        src=r"""
P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. ÉNS (4) 7 (1974), Théorème 4.1 with display (4.1.1), pp. 513–514 (AI-read). The form for normalized eigenforms is F. Diamond and J. Shurman, GTM 228 (2005), Theorem 9.6.6 (numbering unverified).
""",
    ),
    'modularHTCoeff': dict(
        group='modular-galois', slug='kato-hodge-tate-weights',
        title='Hodge–Tate weights of the representation of a newform',
        anchor='Kato Hodge-Tate weights',
        statement=r"""
The *Hodge–Tate weight statement* is the following assertion. Let $\ell$ be a prime, $\iota_{\mathbb C}:\overline{\mathbb Q}\to\mathbb C$ and $\iota_\ell:\overline{\mathbb Q}\to\overline{\mathbb Q}_\ell$ embeddings, and $f$ a newform of weight $k\ge2$ and level $N$; $\ell$ may divide $N$. Then there are a finite extension $E$ of $\mathbb Q_\ell$ inside $\overline{\mathbb Q}_\ell$ and a continuous representation $\rho:G_{\mathbb Q}\to\mathrm{GL}_2(E)$, unramified at every prime $p\nmid N\ell$, for which one of the following holds, where $V=E^2$ with $\rho$ restricted to $G_{\mathbb Q_\ell}$, and $\mathbb C_\ell(w)$ is $\mathbb C_\ell$ with $\sigma$ acting as $\chi_\ell(\sigma)^w\sigma$ for the cyclotomic character $\chi_\ell$: every arithmetic Frobenius at every prime $p\nmid N\ell$ has trace $\iota_\ell\iota_{\mathbb C}^{-1}(a_p(f))$, and $\dim_E(V\otimes_{\mathbb Q_\ell}\mathbb C_\ell(-w))^{G_{\mathbb Q_\ell}}$ is $1$ for $w\in\{0,k-1\}$ and $0$ for every other integer $w$, that is, the Hodge–Tate weights are $0$ and $k-1$ in the convention in which the cyclotomic character has weight $+1$; or every geometric Frobenius at every such prime has trace $\iota_\ell\iota_{\mathbb C}^{-1}(a_p(f))$, and the same holds with $\mathbb C_\ell(w)$ in place of $\mathbb C_\ell(-w)$, that is, the Hodge–Tate weights are $0$ and $k-1$ in the convention in which the cyclotomic character has weight $-1$.
""",
        caveat=r"""
The two alternatives are the two normalizations in which the literature states the theorem. The representation is Deligne's and its Hodge–Tate weights are due to Faltings, Saito and Kato; Kato constructs it over the completion of the coefficient field, at every level. Gee's survey states the existence of the representations attached to regular algebraic cuspidal automorphic representations as a fact, with geometric Frobenius and the cyclotomic character of weight $-1$; reaching the statement from it takes the passage from a newform to its automorphic representation and from de Rham to Hodge–Tate, and a matching of coefficients and embeddings. The statement asks for the traces only. The project's earlier form, over $\overline{\mathbb Q}_\ell$, is proved here from this one. A review of this statement is pending, and no print of the existence form for newforms has been read.
""",
        src=r"""
P. Deligne, Sém. Bourbaki 355 (1969); G. Faltings, Math. Ann. 278 (1987); T. Saito, Invent. Math. 129 (1997); K. Kato, Astérisque 295 (2004), §§9.2–9.4, (9.2.2), pp. 187–188 (read by the locator audit) and §11.3; T. Gee, *Modularity lifting theorems*, Essent. Number Theory 1 (2022), read in arXiv:2202.05818v2: Fact 4.20 in §4.19, p. 28, with the conventions on pp. 2–3 (AI-read); R. Taylor, *Galois representations*, Ann. Fac. Sci. Toulouse Math. (6) 13 (2004). Kato's §11.3, Taylor and the journal numbering of Gee are unverified.
""",
    ),
    'shimuraThm1Af': dict(
        group='modular-galois', slug='shimura-abelian-varieties',
        title="Shimura's abelian variety attached to a newform",
        anchor='Shimura abelian varieties',
        statement=r"""
The *Shimura statement* is the following assertion. Let $f\in S_2(\Gamma_1(N))$ be a newform with character $\chi$, $N\ge2$; let $X$, $P_0$ and $J$ be as in the statement on [Hecke operators](hecke-operators-jacobian.md), and $T_p$ ($p$ prime) and $\langle d\rangle$ ($d\in(\mathbb Z/N)^\times$) endomorphisms of $J$ over $\mathbb Q$ acting by the formulas there. Let $I_f$ be the set of endomorphisms $h(T_p,\langle d\rangle)$ of $J$, for $h$ a polynomial with integer coefficients in noncommuting variables, one for each prime $p$ and each $d$, such that $h(a_p(f),\chi(d))=0$; a homomorphism $\phi$ from $J$ *kills $I_fJ$* when $\phi\circ u=0$ for every $u\in I_f$. For an abelian variety $A$ over $\mathbb Q$, a homomorphism $\nu:J\to A$ and a ring homomorphism $\theta:K_f\to\operatorname{End}^0(A)$, consider the clauses: (i) $\nu$ is surjective and has connected kernel, in the sense that whenever $\nu=\psi\circ\phi$ with $\phi:J\to B$ a surjective homomorphism onto an abelian variety and $\psi:B\to A$ an isogeny, $\psi$ is an isomorphism; (ii) for every prime $p$, $\nu\circ T_p=\theta(a_p(f))\circ\nu$, and for every prime $p\nmid N$, $\nu\circ(T_p^2-p\langle p\rangle)=\theta(a_{p^2}(f))\circ\nu$, both in $\operatorname{Hom}(J,A)\otimes\mathbb Q$, where $\nu\circ t=\theta(a)\circ\nu$ there means that for some integer $m>0$, $m\,\theta(a)$ is an endomorphism $e$ of $A$ with $m(\nu\circ t)=e\circ\nu$; (iii) $\dim A=[K_f:\mathbb Q]$. Then $K_f$ is a number field, and there is a triple $(A,\nu,\theta)$ with (i)–(iii) such that $\nu$ kills $I_fJ$ and every homomorphism from $J$ to an abelian variety that kills $I_fJ$ factors uniquely through $\nu$; and for every triple $(A',\nu',\theta')$ with (i)–(iii) there is an isomorphism $\psi:A\to A'$ over $\mathbb Q$ with $\psi\circ\nu=\nu'$.
""",
        caveat=r"""
Shimura's Theorem 1, for a normalized eigenform of all the $T_n$ on any group between $\Gamma_1(N)$ and $\Gamma_0(N)$, constructs the quotient $A=J/C$ with $C=\ker\nu$, builds $C$ from the ideal of the Hecke ring annihilating $f$ intersected with $\operatorname{End}(J)$, gives (i)–(iii) with $\nu\circ\xi_n=\theta(a_n)\circ\nu$ for every $n$, and states that under (i) and (ii) the triple is unique up to isomorphism over $\mathbb Q$; an AI reading of the print found these on pp. 525–527. Three steps are made on the spot: that $C$ is $I_fJ$, through a saturation argument and the Hecke relations between Shimura's $\xi_n$ and the $T_p$, $\langle d\rangle$; that (ii) at $n=p$ and $n=p^2$, with $\xi_{p^2}=T_p^2-p\langle p\rangle$, gives (ii) for every $n$, so that the triples of the uniqueness clause are Shimura's; and that his isomorphism is compatible with $\nu$. The uniqueness clause here compares only triples that also satisfy (iii), which weakens the printed one. The statement takes $\Gamma=\Gamma_1(N)$ and newforms, takes $T_p$ to be Shimura's $\xi_p$ through the identifications of the statement on Hecke operators, and omits his clauses on the cotangent space and on the zeta function of $A$. Diamond and Shurman define $A_f$ as $J/I_fJ$ over $\mathbb C$. A review of this statement is pending.
""",
        src=r"""
G. Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc. Japan 25 (1973), 523–544, Theorem 1, p. 526, with its construction and proof, pp. 525–527 (AI page read): $C=\operatorname{Ker}(\nu)$, p. 525; $C$ from the ideal annihilating $f$ intersected with $\operatorname{End}(J)$, and uniqueness under (i) and (ii) up to isomorphisms over $\mathbb Q$, p. 526; multiplicity one from $q$-expansions, p. 527. A sentence on p. 526 that the statement does not use has a harmless misprint, "$f_\sigma\mid T_n=a_n^\sigma f$" for "$f_\sigma\mid T_n=a_n^\sigma f_\sigma$". F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228 (2005), Definition 6.6.3, p. 241 (AI-read).
""",
    ),
}
