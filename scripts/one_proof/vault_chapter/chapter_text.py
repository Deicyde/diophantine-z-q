"""Prose for blueprint/roadmap/height-decomposition/ (fork main 0caafe66, leaf-fold31).

One entry per field of the four H bundles. `gen.py` refuses to run when the fields of
open-statements.json and this file differ, so each fold forces an edit here.
"""

GROUPS = [
    dict(dir='shimura-curves', title='Shimura curves of discriminant 6', intro=r"""
Let $B=\left(\frac{2,-3}{\mathbb Q}\right)$ be the quaternion algebra over $\mathbb Q$ of discriminant
$6$ and $\mathcal O$ a maximal order of $B$. A *QM abelian surface* over a field is an abelian surface
$A$ with an embedding $\iota:\mathcal O\to\operatorname{End}(A)$. The Shimura curve $X_6=X_0(6,1)$ is a
coarse moduli space for these pairs, and $Y_3$ a fine moduli scheme for the pairs with a level-$3$
structure; the automorphisms of $\mathcal O$ act on the pairs, and through them the Atkin–Lehner group
$W=\{1,w_2,w_3,w_6\}$ acts on $X_6$. These four statements describe the two curves: their complex
uniformization and Shimura's reciprocity law at CM points, the residue fields and the number of the CM
points of $X_6$, and Elkies' coordinate on $X_6/W$.

Throughout, a *moduli pair* is a pair of proper smooth curves $Y$ and $X$ over $\mathbb Q$, each with
a $\overline{\mathbb Q}$-point, with a morphism $Y\to X$, such that: $Y$ is a fine moduli scheme for QM
abelian surfaces with level-$3$ structure, with its moduli properties stated for abelian schemes and
compatible with extension of the base field; $X(\overline{\mathbb Q})$ is in Galois-equivariant
bijection with the isomorphism classes of QM abelian surfaces over $\overline{\mathbb Q}$, and every
automorphism of $\mathcal O$ acts on these classes through an automorphism of $X$ over $\mathbb Q$; and
$Y\to X$ forgets the level structure on $\overline{\mathbb Q}$-points. For a QM abelian surface
$(A,\iota)$, $\operatorname{End}_{\mathcal O}(A)$ is the ring of endomorphisms commuting with
$\iota(\mathcal O)$; the pair has *CM by an order* $R$ of an imaginary quadratic field when this ring
is isomorphic to $R$.
"""),
    dict(dir='theta-constants', title='Theta constants of genus 2', intro=r"""
For a matrix $\Omega$ in the Siegel upper half-space $\mathfrak H_2$ and a characteristic $m$, the
theta constant $\theta_m(0,\Omega)$ is the value at $0$ of the theta function with characteristic $m$.
The proof reads a height off the theta constants of a period matrix of an abelian surface; the one
statement of this group says that their ratios are algebraic when the surface is defined over a number
field.
"""),
    dict(dir='abelian-varieties', title='Abelian varieties', intro=r"""
Statements about abelian varieties over a field: the torsion, the homomorphisms and the characteristic
polynomials of endomorphisms over an algebraically closed field (Mumford), Poincaré's complete
reducibility, quasi-inverses of isogenies, Mumford's criterion for a family to be an abelian scheme,
the analytic uniformization over $\mathbb C$ and GAGA for its homomorphisms, and four statements on the
Picard scheme of an abelian variety and the Weil pairing, from which the proof builds a symmetric
isogeny to the dual.
"""),
    dict(dir='neron-models', title='Néron models, semistable reduction and monodromy', intro=r"""
Let $\mathcal O$ be a discrete valuation ring with fraction field $K$ and $A$ an abelian variety over
$K$. A *Néron model* of $A$ is a smooth separated group scheme of finite type over $\mathcal O$ with
generic fibre $A$ to which every morphism from the generic fibre of a smooth $\mathcal O$-scheme to $A$
extends uniquely; $A$ has *semistable reduction* when the identity component of the special fibre of
its Néron model is an extension of an abelian variety by a torus. These statements give the existence
of Néron models, their compatibility with strict henselization, the criterion of
Néron–Ogg–Shafarevich, Raynaud's criterion for semistable reduction, and two results of SGA 7, Exposé
IX, on semistable reduction over a strictly henselian base.
"""),
    dict(dir='group-schemes', title='Schemes and group schemes over a field', intro=r"""
Standard facts about group schemes (Cartier's theorem, equidimensionality, the openness of the identity
component) and about schemes over a field, and one statement of EGA IV on limits of schemes.
"""),
    dict(dir='heights', title='Faltings 1983 and Faltings heights', intro=r"""
Faltings' theorems of 1983 on Tate modules, and four bounds for the stable Faltings height of an
abelian variety over a number field. Heights are in Faltings' normalization $h_F$; Deligne's
normalization is $h_D=h_F+\frac g2\log\pi$ for an abelian variety of dimension $g$. The stable
Faltings height is used in the project's definition, through a definition of semistability; that the
two agree with the published definitions is a judgement of AI reviews.
"""),
    dict(dir='p-adic-hodge', title='p-adic Hodge theory', intro=r"""
Let $p$ be a prime, $\overline{\mathbb Q}_p$ an algebraic closure of $\mathbb Q_p$ and $\mathbb C_p$
its completion. For a finite extension $K$ of $\mathbb Q_p$, $G_K$ is its absolute Galois group and
$\mathbb C_p(i)$ the twist of $\mathbb C_p$ by the $i$-th power of the cyclotomic character. These
statements give Tate's computation of the Galois invariants of $\mathbb C_p$ and its twists, the
Hodge–Tate decomposition and the de Rham comparison for abelian varieties, and Pan's
Fontaine–Mazur theorem for two-dimensional representations.
"""),
    dict(dir='modular-galois', title='Galois representations of modular forms', intro=r"""
Fix embeddings $\iota_{\mathbb C}:\overline{\mathbb Q}\to\mathbb C$ and
$\iota_\ell:\overline{\mathbb Q}\to\overline{\mathbb Q}_\ell$. A continuous representation
$\rho:G_{\mathbb Q}\to\mathrm{GL}_2(\overline{\mathbb Q}_\ell)$ is *attached* to a normalized eigenform
$f$ of level $N$ when, at every prime $p\nmid N\ell$, it is unramified and the trace of an arithmetic
Frobenius at $p$ is $\iota_\ell\iota_{\mathbb C}^{-1}(a_p(f))$. These statements give the
representations attached to eigenforms of weight $k\ge2$ (Deligne) and of weight $1$
(Deligne–Serre), their Hodge–Tate weights (Kato), their conductors (Carayol), and Shimura's abelian
varieties attached to newforms of weight $2$.
"""),
]

LEAVES = {
    # ----- shimura-curves -----
    'gonzalezRotgerX6Ab': dict(
        group='shimura-curves', slug='gonzalez-rotger-residue-fields',
        title='González–Rotger: residue fields of CM points on X₆',
        anchor='Gonzalez-Rotger Theorem 5.12',
        statement=r"""
The *González–Rotger statement on residue fields* is the following assertion. There is a moduli pair
$(Y,X)$ such that the following holds. Let $k$ be an imaginary quadratic field, $R$ an order of $k$
whose conductor is prime to $6$, and $x\in X(\overline{\mathbb Q})$ a point whose QM abelian surface
has CM by $R$. If $2$ or $3$ is inert in $k$, the residue field $\mathbb Q(x)$ has degree $2h(R)$ over
$\mathbb Q$ and contains a copy of $k$; otherwise it has degree $h(R)$. Here $h(R)$ is the order of the
Picard group of $R$.
""",
        caveat=r"""
This is Theorem 5.12 of González and Rotger (2006) on $X_0(6,1)$, with the moduli properties of the
level-$3$ curve stated for abelian schemes. It also asserts that a moduli pair exists.
""",
        src=r"""
J. González and V. Rotger, *Non-elliptic Shimura curves of genus one*, J. Math. Soc. Japan 58 (2006),
Theorem 5.12, on the residue fields of the CM points of $X_0(6,1)$, in its printed form; the theorem
number was read by the locator audit, but the locator is still marked unverified.
"""),
    'gonzalezRotgerProp56X6': dict(
        group='shimura-curves', slug='gonzalez-rotger-cm-count',
        title='González–Rotger: the number of CM points on X₆',
        anchor='Gonzalez-Rotger Proposition 5.6',
        statement=r"""
The *González–Rotger count* is the following assertion. Let $(Y,X)$ be a moduli pair, $k$ an
imaginary quadratic field and $R$ an order of $k$ whose conductor is prime to $6$, and suppose that
some QM abelian surface over $\overline{\mathbb Q}$ has CM by $R$. Then the number of points
$x\in X(\overline{\mathbb Q})$ whose QM abelian surface has CM by $R$ is $2^{b}h(R)$, where $b$ is the
number of primes dividing $6$ that are inert in $k$ and $h(R)$ is the order of the Picard group of $R$.
""",
        caveat=r"""
This is Proposition 5.6 of González and Rotger at $(D,N)=(6,1)$, stated for every moduli pair; it
asserts nothing about the existence of one. The hypothesis that $R$ occurs is the moduli form of the
printed hypothesis that $R$ embeds optimally in $\mathcal O$. The proposition was read by the locator
audit, but its wording has not been checked against the paper by the statement review: a reader with
the paper should confirm that their $D(R)$ is the product of the primes $p\mid6$ with $(R/p)=-1$.
""",
        src=r"""
J. González and V. Rotger, J. Math. Soc. Japan 58 (2006), Proposition 5.6, p. 943, at $(D,N)=(6,1)$,
read by the locator audit; restated for every moduli description of $X_0(6,1)$. The reading of $D(R)$
is to be confirmed against the paper.
"""),
    'elkiesX6StarFunctionField': dict(
        group='shimura-curves', slug='elkies-coordinate',
        title="Elkies' coordinate on X₆/W",
        anchor='Elkies coordinate',
        statement=r"""
The *Elkies statement* is the following assertion. There are a moduli pair $(Y,X)$ and a rational
function $t$ on $X$ such that: if $X$ is integral and $t$ is defined at its generic point, the field
of rational functions on $X$ fixed by $W$, acting through its moduli action, is $\mathbb Q(t)$; $t$
takes the value $0$ at the points whose QM abelian surface has CM by the order of discriminant $-24$,
the value $1$ at those with CM of discriminant $-4$, and the value $\infty$ at those with CM of
discriminant $-3$; and $X$ is covered, over the $t$-line, by Elkies' charts $s^2=-t$ and
$r^2=3(t-1)$.
""",
        caveat=r"""
This is what the project takes to be Elkies' own wording, the equality of function fields
$\mathbb Q(X_6)^W=\mathbb Q(t)$; it has not yet been read against his paper, and the section, the
display and the orientation of $0$ and $\infty$ are unverified.
""",
        src=r"""
N. D. Elkies, *Shimura curve computations*, ANTS-III, LNCS 1423 (1998), section 3, on
$X^*(6)=X_6/W$ with coordinate $t$: the function-field form $\mathbb Q(X_6)^W=\mathbb Q(t)$, the CM
values and the equations of $X_6$ over the $t$-line. Section, display and the orientation of $0$ and
$\infty$ unverified.
"""),
    'shimuraMainThmIDeligneY3AbU': dict(
        group='shimura-curves', slug='shimura-main-theorem-y3',
        title="Shimura's Main Theorem I on Y₃ in Deligne's form",
        anchor='Shimura Main Theorem I in Deligne form',
        statement=r"""
The *Shimura–Deligne statement on $Y_3$* is the following assertion. Let $K_3$ be the level-$3$
subgroup of $(B\otimes\mathbb A_f)^\times$ and $\widehat{\mathcal O}^\times$ the units of the
completion of $\mathcal O$. There is a fine moduli scheme $Y_3$ over $\mathbb Q$ for QM abelian
surfaces with level-$3$ structure, with its moduli properties stated for abelian schemes, with a
bijection
$$B^\times_+\backslash\bigl(\mathfrak H\times(B\otimes\mathbb A_f)^\times\bigr)/K_3\;\cong\;Y_3(\mathbb C),
\qquad(\tau,u)\mapsto\Psi(\tau,u),$$
holomorphic in $\tau$, such that for every $u\in\widehat{\mathcal O}^\times$ the QM abelian surface at
$\Psi(\tau,u)$ is $\mathbb C^2/\iota(\mathcal O)(\tau,1)^{T}$, and Shimura's reciprocity law holds at
the CM points.
""",
        caveat=r"""
It combines Shimura's Main Theorem I (1967), his reciprocity law at CM points, with Deligne's adelic
form of the canonical model and the fine moduli of QM abelian surfaces with level-$3$ structure.
""",
        src=r"""
G. Shimura, Ann. of Math. 85 (1967), Main Theorem I (reciprocity at CM points); P. Deligne, Sém.
Bourbaki 389 (1971), sections 4.9–4.21 and 5 (the adelic form and the canonical model; the PEL model is
Corollary 5.7 and Example 5.8, not Theorem 4.21, which is the Siegel case); J. S. Milne, *Introduction
to Shimura varieties*, sections 12–14; with the fine moduli of QM abelian surfaces with level-$3$
structure. Locators unverified.
"""),
    # ----- theta-constants -----
    'thetaRatiosAlgebraic': dict(
        group='theta-constants', slug='theta-ratios-algebraic',
        title='Ratios of theta constants are algebraic',
        anchor='Theta ratios',
        statement=r"""
The *theta-ratio statement* is the following assertion. Let $A$ be an abelian surface over a number
field $K$, $\sigma:K\to\mathbb C$ an embedding, $\Phi:\mathbb C^2\to A_\sigma(\mathbb C)$ a
uniformization with kernel $\Lambda$, and $\Omega\in\mathfrak H_2$ a period matrix of $\Lambda$. Then
some theta constant $\theta_{m_0}(0,\Omega)$ is nonzero, and every ratio
$\theta_m(0,\Omega)/\theta_{m_0}(0,\Omega)$ is an algebraic number.
""",
        caveat=r"""
It combines Shimura's theorem that the values of Siegel modular functions with algebraic Fourier
coefficients at a point whose principally polarized abelian variety is defined over
$\overline{\mathbb Q}$ are algebraic (for genus $2$ also Thomae's formula), the equality of the
Néron–Severi groups of $A$ over $\overline{\mathbb Q}$ and over $\mathbb C$ for the polarization that
$\Omega$ defines, and Igusa's theorem that at most one of the ten even theta constants vanishes in
genus $2$.
""",
        src=r"""
G. Shimura, Duke Math. J. 43 (1976); D. Mumford, *Tata Lectures on Theta II*, IIIa §8 (Thomae's
formula in genus 2); J. Igusa (1962, 1967) on the vanishing of even theta constants. Locators
unverified.
"""),
    # ----- abelian-varieties -----
    'mumfordTorsionAlgClosed': dict(
        group='abelian-varieties', slug='torsion-points',
        title='Torsion points over an algebraically closed field',
        anchor='Mumford torsion',
        statement=r"""
The *torsion statement* is the following assertion. Let $X$ be an abelian variety of dimension $g$
over an algebraically closed field $k$ and $n\ge1$ an integer with $n\ne0$ in $k$. Then the group of
points $x\in X(k)$ with $nx=0$ is isomorphic to $(\mathbb Z/n\mathbb Z)^{2g}$.
""",
        caveat='',
        src=r"""
D. Mumford, *Abelian varieties* (1970; 2nd ed. 1974), §4, Application 2 (iv). Locator unverified.
"""),
    'homFreeFiniteAlgClosed': dict(
        group='abelian-varieties', slug='homomorphisms-and-tate-modules',
        title='Homomorphisms of abelian varieties and Tate modules',
        anchor='Mumford homomorphisms',
        statement=r"""
The *homomorphism statement* is the following assertion. Let $X$ and $Y$ be abelian varieties over an
algebraically closed field $k$. Then $\operatorname{Hom}(X,Y)$ is a free $\mathbb Z$-module of finite
rank at most $4\dim X\dim Y$, and for every prime $\ell\ne\operatorname{char}k$ the natural map
$\mathbb Z_\ell\otimes\operatorname{Hom}(X,Y)\to\operatorname{Hom}_{\mathbb Z_\ell}(T_\ell X,T_\ell Y)$
is injective.
""",
        caveat='',
        src=r"""
D. Mumford, *Abelian varieties* (1970), §19, Theorem 3 (the ground field is algebraically closed
throughout the book). Locator unverified.
"""),
    'charPolyIndepOfEllAlgClosed': dict(
        group='abelian-varieties', slug='characteristic-polynomial',
        title='The characteristic polynomial of an endomorphism',
        anchor='Mumford characteristic polynomial',
        statement=r"""
The *characteristic-polynomial statement* is the following assertion. Let $X$ be an abelian variety
over an algebraically closed field $k$ and $\varphi$ an endomorphism of $X$. Then there is a monic
polynomial $P\in\mathbb Z[T]$ that is the characteristic polynomial of $T_\ell(\varphi)$ on the Tate
module $T_\ell X$ for every prime $\ell\ne\operatorname{char}k$.
""",
        caveat=r"""
It is part of Mumford's theorem, which also gives that $P$ has degree $2\dim X$ and that
$P(n)=\deg(n-\varphi)$ for every integer $n$.
""",
        src=r"""
D. Mumford, *Abelian varieties* (1970), §19, Theorem 4, specialized. Locator unverified.
"""),
    'poincareComplement': dict(
        group='abelian-varieties', slug='poincare-complement',
        title="Poincaré's complete reducibility",
        anchor='Poincare complete reducibility',
        statement=r"""
The *Poincaré statement* is the following assertion. Let $J$ be an abelian variety over a field of
characteristic $0$ and $i:B\to J$ a homomorphism of abelian varieties that is a closed immersion. Then
there are an abelian variety $Z$ and a homomorphism $j:Z\to J$ such that $B\times Z\to J$,
$(b,z)\mapsto i(b)+j(z)$, is an isogeny.
""",
        caveat=r"""
It is weaker than the published statement: the characteristic is $0$, and it does not assert that
$j$ is a closed immersion.
""",
        src=r"""
J. S. Milne, *Abelian varieties*, in Cornell–Silverman (eds.), *Arithmetic Geometry* (1986),
Proposition 12.1, over any field; over an algebraically closed field D. Mumford, *Abelian varieties*
(1970), §19, Theorem 1. Locators unverified.
"""),
    'milneIsogenyQuasiInverse': dict(
        group='abelian-varieties', slug='isogeny-quasi-inverse',
        title='A quasi-inverse of an isogeny',
        anchor='Milne quasi-inverse',
        statement=r"""
The *quasi-inverse statement* is the following assertion. Let $f:A\to B$ be a homomorphism of abelian
varieties over a field that is finite and surjective. Then there are an integer $d\ge1$ and a
homomorphism $g:B\to A$ with $g\circ f=[d]_A$ and $f\circ g=[d]_B$.
""",
        caveat=r"""
It is read off Milne's display, which takes $d=\deg f$ and also gives that $g$ is an isogeny.
""",
        src=r"""
J. S. Milne, *Abelian varieties*, in Cornell–Silverman (eds.), *Arithmetic Geometry* (1986), §8,
Remark 8.4; also Milne's online notes *Abelian Varieties* (2008), Proposition 7.1 and Remark 7.3;
over an algebraically closed field D. Mumford, *Abelian varieties* (1970), §7, remark after Theorem 4.
Locators unverified.
"""),
    'mumfordGroupLaw': dict(
        group='abelian-varieties', slug='mumford-group-law',
        title="Mumford's theorem: families of abelian varieties are abelian schemes",
        anchor='Mumford GIT Theorem 6.14',
        statement=r"""
The *group-law statement* is the following assertion. Let $S$ be a locally noetherian scheme and
$F\to S$ a proper smooth morphism with geometrically connected fibres and a section $e$, such that
the fibre of $F$ over every point $s\in S$ is an abelian variety over the residue field of $s$ with
identity $e(s)$. Then $F$ is a group scheme over $S$ with identity $e$.
""",
        caveat=r"""
Mumford's theorem is stated for a connected base; the statement applies it on each connected
component of $S$. A statement review of this form as the print is pending.
""",
        src=r"""
D. Mumford, J. Fogarty and F. Kirwan, *Geometric Invariant Theory*, Theorem 6.14 ($S$ connected and
locally noetherian, $F\to S$ smooth and proper with a section $e$, a fibre an abelian variety: $F$ is
an abelian scheme with identity $e$), applied on each connected component. Numbers unverified.
"""),
    'uniformizationLeafAll': dict(
        group='abelian-varieties', slug='analytic-uniformization',
        title='The analytic uniformization of a complex abelian variety',
        anchor='Analytic uniformization',
        statement=r"""
The *uniformization statement* is the following assertion. For every abelian variety $A$ over
$\mathbb C$ there are an integer $g$, a lattice $\Lambda\subset\mathbb C^g$ (a discrete subgroup of
rank $2g$) and a group isomorphism $\varphi:\mathbb C^g/\Lambda\to A(\mathbb C)$ that is an
isomorphism of complex Lie groups in the following sense: every regular function on a Zariski open
subset of $A$ pulls back along $\varphi$ to a holomorphic function on an open subset of
$\mathbb C^g$; at every point, some $g$ regular functions pull back to local holomorphic coordinates;
and $\varphi^{-1}$ is continuous for the topology on $A(\mathbb C)$ that the regular functions define.
""",
        caveat=r"""
The printed theorem says that a compact connected complex Lie group is a torus; applying it to the
analytic space of $A$, in these coordinates, takes the analytification and GAGA.
""",
        src=r"""
D. Mumford, *Abelian varieties*, §1 ($A^{\rm an}=\mathbb C^g/\Lambda$), in coordinate form, reached
through the analytification and GAGA.
"""),
    'gagaMorphism': dict(
        group='abelian-varieties', slug='gaga-for-homomorphisms',
        title='GAGA for homomorphisms of complex abelian varieties',
        anchor='GAGA for homomorphisms',
        statement=r"""
The *GAGA statement* is the following assertion. Let $A$ and $B$ be abelian varieties over $\mathbb C$,
$\varphi:\mathbb C^g/\Lambda\to A(\mathbb C)$ a uniformization of $A$ as in
[the uniformization statement](analytic-uniformization.md), and $\psi:\mathbb C^g\to B(\mathbb C)$ a
holomorphic homomorphism that vanishes on $\Lambda$. Then the map $A(\mathbb C)\to B(\mathbb C)$ that
$\psi$ induces comes from a morphism of varieties $A\to B$.
""",
        caveat='',
        src=r"""
J.-P. Serre, *Géométrie algébrique et géométrie analytique* (1956); SGA 1 XII 4.4
($\operatorname{Hom}(X,Y)\to\operatorname{Hom}(X^{\rm an},Y^{\rm an})$ is bijective for $X$ proper over
$\mathbb C$). Locators unverified.
"""),
    'picRepresentableAbVar': dict(
        group='abelian-varieties', slug='picard-scheme-exists',
        title='The Picard scheme of an abelian variety',
        anchor='Picard scheme',
        statement=r"""
The *Picard statement* is the following assertion. For an abelian variety $A$ over a field $K$, the
relative Picard functor of $A$ over $K$, as an fppf sheaf, is representable by a scheme
$\operatorname{Pic}_{A/K}$.
""",
        caveat=r"""
A statement review of this form is pending; one model review found no errors.
""",
        src=r"""
J. P. Murre (1964) and F. Oort (1962); A. Grothendieck, FGA, Exposé 232, Theorem 3.1; S. Kleiman,
*The Picard scheme*, Theorem 9.4.8 with 9.2.5. Locators unverified.
"""),
    'picZeroAbVar': dict(
        group='abelian-varieties', slug='identity-component-of-picard',
        title='The identity component of the Picard scheme is an abelian variety',
        anchor='Identity component of the Picard scheme',
        statement=r"""
The *dual statement* is the following assertion. Let $A$ be an abelian variety over a field $K$. For
every scheme representing the relative Picard functor of $A$, its identity component, with the
induced group law, is an abelian variety $\operatorname{Pic}^0_{A/K}$.
""",
        caveat=r"""
Mumford builds the dual abelian variety over an algebraic closure of $K$; identifying it with the
identity component of $\operatorname{Pic}_{A/K}$ and descending to $K$ are theorem steps (Kleiman
9.5.1; SGA 3, Exposé VI_A, 2.4). One printed statement over an arbitrary field in this form would make
it a published statement (candidates: Bosch–Lütkebohmert–Raynaud 8.4; *FGA Explained* 9.5; Milne 1986,
§10).
""",
        src=r"""
D. Mumford, *Abelian varieties*, §13; S. Kleiman, *The Picard scheme*, Propositions 9.5.1 and 9.5.3;
J. S. Milne (1986), §§9–10. Locators unverified.
"""),
    'phiAmpleIsogeny': dict(
        group='abelian-varieties', slug='polarization-isogeny',
        title='The polarization of an ample line bundle is an isogeny',
        anchor='Polarization isogeny',
        statement=r"""
The *polarization statement* is the following assertion. Let $A$ be an abelian variety over a field
$K$ and $L$ an ample line bundle on $A$. Then the morphism $\lambda_L:A\to\operatorname{Pic}^0_{A/K}$,
$x\mapsto t_x^*L\otimes L^{-1}$, is finite and surjective.
""",
        caveat=r"""
Mumford's theorems are stated over an algebraically closed field and about points; reaching the
statement needs Mumford's dual identified with $\operatorname{Pic}^0_{A/K}$, fpqc descent from the
algebraic closure (EGA IV 2.7.1), that a proper quasi-finite morphism is finite, and the passage
from effective divisors to an arbitrary ample $L$.
""",
        src=r"""
D. Mumford, *Abelian varieties*, §6, Application 1, and §8, Theorem 1. Locators unverified.
"""),
    'weilPairingMumford': dict(
        group='abelian-varieties', slug='weil-pairing',
        title='The Weil pairing',
        anchor='Weil pairing',
        statement=r"""
The *Weil-pairing statement* is the following assertion. Let $A$ be an abelian variety over a field
$K$ and $n\ge1$ an integer invertible in $K$. Then there is a pairing
$A[n]\times\operatorname{Pic}^0_{A/K}[n]\to\mu_n$ with the values of Mumford's pairing $\bar e_n$
that is perfect, Galois-equivariant and compatible in $n$, adjoint for the dual $f^\vee$ of every
homomorphism $f$, and trivial on the pairs $(x,\lambda_L x)$ for every ample line bundle $L$.
""",
        caveat=r"""
The printed pairing is on Mumford's dual; reading it on $\operatorname{Pic}^0_{A/K}$ passes through
Kleiman 9.2.5 and Mumford §8 (iv), §8 Theorem 1 and §13, with base change to an algebraic closure,
and the statement also combines several sources (Mumford §§20 and 23, Milne 1986 §16). The sign
convention does not matter.
""",
        src=r"""
D. Mumford, *Abelian varieties*, §§20 and 23; J. S. Milne (1986), Lemma 16.2(c) and §16. Locators
unverified.
"""),
    # ----- neron-models -----
    'neronSchemeExtensionExists': dict(
        group='neron-models', slug='neron-models-exist',
        title='Néron models over rings of integers',
        anchor='Neron models exist',
        statement=r"""
The *Néron existence statement* is the following assertion. Let $A$ be an abelian variety over a field
$K$ and $L$ a number field containing $K$, with ring of integers $\mathcal O_L$. Then there is a smooth,
separated, quasi-compact scheme $N$ over $\mathcal O_L$ with generic fibre $A_L$ such that, for every
smooth $\mathcal O_L$-scheme $Y$, every morphism $Y_L\to A_L$ extends to a morphism $Y\to N$.
""",
        caveat=r"""
It asks only for the existence of the extension, which is unique since $Y$ is flat over $\mathcal O_L$
and $N$ is separated, so it is weaker than the existence of Néron models.
""",
        src=r"""
S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, §1.4, Theorem 3, with §1.2, Definition 1.
Locators unverified.
"""),
    'neronBaseChangeStrictHenselization': dict(
        group='neron-models', slug='neron-models-and-strict-henselization',
        title='Néron models commute with strict henselization',
        anchor='Neron models and strict henselization',
        statement=r"""
The *strict henselization statement* is the following assertion. Let $\mathcal O\to\mathcal O'$ be an
unramified extension of discrete valuation rings, with fraction fields $K\subset K'$, such that
$\mathcal O'$ is strictly henselian and its residue field is separable over that of $\mathcal O$, and
let $A$ be an abelian variety over $K$ with a Néron model $N$ over $\mathcal O$. Then
$N\times_{\mathcal O}\mathcal O'$ is a Néron model of $A_{K'}$.
""",
        caveat=r"""
The hypotheses make $\mathcal O'$ a strict henselization of $\mathcal O$; the commutative algebra
behind this is proved here.
""",
        src=r"""
S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, §1.2, Proposition 2 (Néron models commute
with strict henselization). Locator unverified.
"""),
    'r7a': dict(
        group='neron-models', slug='neron-ogg-shafarevich',
        title='The criterion of Néron–Ogg–Shafarevich',
        anchor='Neron-Ogg-Shafarevich',
        statement=r"""
The *Néron–Ogg–Shafarevich statement* is the following assertion. Let $K$ be a field, $\mathcal O$ a
discrete valuation ring with fraction field $K$, $w$ a valuation ring of $\overline K$ over
$\mathcal O$, and $A$ an abelian variety over $K$. Then the following are equivalent: $A$ has good
reduction at $\mathcal O$; for every integer $m\ge1$ invertible in $\mathcal O$, the inertia group at
$w$ acts trivially on $A(\overline K)[m]$; the same holds for infinitely many such $m$.
""",
        caveat='',
        src=r"""
J.-P. Serre and J. Tate, *Good reduction of abelian varieties*, Ann. of Math. 88 (1968), Theorem 1.
Locator unverified.
"""),
    'raynaudSemistableSH': dict(
        group='neron-models', slug='raynaud-criterion',
        title="Raynaud's criterion for semistable reduction",
        anchor='Raynaud criterion',
        statement=r"""
The *Raynaud statement* is the following assertion. Let $\mathcal O$ be a strictly henselian discrete
valuation ring with fraction field $K$, $A$ an abelian variety over $K$ and $m\ge3$ an integer
invertible in $\mathcal O$. If every point of $A$ of order dividing $m$ is rational over $K$, then $A$
has semistable reduction at $\mathcal O$.
""",
        caveat=r"""
The residue field is arbitrary. If the print assumes an algebraically closed residue field, this
form is stronger than the print for imperfect residue fields; the review of the next fold rated that
risk low.
""",
        src=r"""
SGA 7 I, Exposé IX, Proposition 4.7 (Raynaud's criterion), over a strictly henselian discrete
valuation ring; with the strict henselization statement it gives the criterion over every discrete
valuation ring. Number unverified.
"""),
    'sga7_IX_3_3_SH': dict(
        group='neron-models', slug='semistable-base-change',
        title='Semistable reduction persists under base change',
        anchor='SGA 7 IX 3.3',
        statement=r"""
The *base-change statement* is the following assertion. Let $\mathcal O\to\mathcal O'$ be a local
extension of strictly henselian discrete valuation rings with fraction fields $K\subset K'$, and $A$ an
abelian variety over $K$ with semistable reduction, with Néron models $N$ over $\mathcal O$ and $N'$ of
$A_{K'}$ over $\mathcal O'$. Then the canonical morphism $N^0\times_{\mathcal O}\mathcal O'\to N'^0$
of identity components is an isomorphism.
""",
        caveat=r"""
SGA 7 IX 3.3 may assume an algebraically closed residue field; then this form is not the print, and
another reading of the source (a variant over algebraically closed residue fields, or
Bosch–Lütkebohmert–Raynaud 7.4) has to cover it.
""",
        src=r"""
SGA 7 I, Exposé IX, Proposition 3.3, second assertion, over strictly henselian traits. Number
unverified.
"""),
    'sga7_IX_3_5_ForwardGeom': dict(
        group='neron-models', slug='semistable-unipotent-inertia',
        title='Semistable reduction gives unipotent inertia',
        anchor='SGA 7 IX 3.5',
        statement=r"""
The *unipotence statement* is the following assertion. Let $\mathcal O$ be a strictly henselian
discrete valuation ring with fraction field $K$ and separable closure $K^s$ of $K$, $\ell$ a prime
invertible in $\mathcal O$, and $A$ an abelian variety over $K$ whose geometric special fibre is
semistable. Then $(\sigma-1)^2=0$ on $T_\ell A=\varprojlim A(K^s)[\ell^n]$ for every
$\sigma\in\operatorname{Gal}(K^s/K)$.
""",
        caveat=r"""
The print gives $(\sigma-1)(\tau-1)=0$ for any two elements of inertia, and the converse; this is
the forward direction at $\sigma=\tau$. If the print reads semistability on the special fibre over
its own residue field, this form exceeds it for imperfect residue fields only, and if its display
lacks the clause on filtrations, the bound comes from SGA 7 IX 2.4.
""",
        src=r"""
SGA 7 I, Exposé IX, Proposition 3.5, forward direction at $\sigma=\tau$, over a strictly henselian
discrete valuation ring. Number unverified.
"""),
    # ----- group-schemes -----
    'cartierSmooth': dict(
        group='group-schemes', slug='cartier-theorem',
        title="Cartier's theorem",
        anchor='Cartier theorem',
        statement=r"""
The *Cartier statement* is the following assertion. A group scheme locally of finite type over a field
of characteristic $0$ is smooth.
""",
        caveat='',
        src=r"""
P. Cartier, *Groupes algébriques et groupes formels*, Colloque Bruxelles (1962); F. Oort, Invent.
Math. 2 (1966), 79–80; D. Mumford, *Abelian varieties*, §11, Theorem 1; J. S. Milne, *Algebraic Groups*
(2017), Theorem 3.23; Stacks Project, Tag 047N. Locators unverified.
"""),
    'groupSchemeEquidim': dict(
        group='group-schemes', slug='group-schemes-equidimensional',
        title='Group schemes over a field are equidimensional',
        anchor='Group schemes are equidimensional',
        statement=r"""
The *equidimensionality statement* is the following assertion. For a group scheme $G$ of finite type
over a field, every irreducible component of $G$ has dimension $\dim G$.
""",
        caveat='',
        src=r"""
Stacks Project, Groupoid schemes, properties of group schemes over a field; SGA 3, Exposé VI_A, 2.4;
J. S. Milne, *Algebraic Groups* (2017), Proposition 1.37. Locators unverified.
"""),
    'sga3_VIB_3_10': dict(
        group='group-schemes', slug='identity-component-open',
        title='The identity component of a smooth group scheme is open',
        anchor='SGA 3 VI_B 3.10',
        statement=r"""
The *identity-component statement* is the following assertion. For a smooth group scheme $G$ over a
scheme $S$, the union $G^0$ of the identity components of the fibres of $G$ is open in $G$.
""",
        caveat='',
        src=r"""
SGA 3, Exposé VI_B, 3.10. Number unverified.
"""),
    'geomConnOfRationalPoint': dict(
        group='group-schemes', slug='geometrically-connected',
        title='A connected scheme with a rational point is geometrically connected',
        anchor='Geometric connectedness',
        statement=r"""
The *connectedness statement* is the following assertion. A connected scheme of finite type over a
field $k$ with a $k$-rational point is geometrically connected.
""",
        caveat=r"""
The Stacks Project states it without the finiteness hypothesis and for a point whose residue field
contains $k$ algebraically closed in it; a rational point is such a point.
""",
        src=r"""
Stacks Project, Varieties, Lemma 33.7.14 (Tag 04KV). Locator unverified.
"""),
    'egaIV_8_10_5_xii': dict(
        group='group-schemes', slug='properness-spreads-out',
        title='Properness spreads out from a limit',
        anchor='EGA IV 8.10.5 (xii)',
        statement=r"""
The *spreading-out statement* is the following assertion. Let $(D_i)$ be a filtered inverse system of
quasi-compact quasi-separated schemes with affine transition morphisms and limit $D$, and $X_i$ a
scheme of finite presentation over $D_i$. If $X_i\times_{D_i}D$ is proper over $D$, then
$X_i\times_{D_i}D_j$ is proper over $D_j$ for some $j\ge i$.
""",
        caveat='',
        src=r"""
EGA IV₃, 8.10.5 (xii); also Stacks Project, Tag 081F. Locators unverified, quoted from memory.
"""),
    # ----- heights -----
    'r9a': dict(
        group='heights', slug='faltings-semisimplicity',
        title="Faltings' semisimplicity theorem",
        anchor='Faltings semisimplicity',
        statement=r"""
The *semisimplicity statement* is the following assertion. For an abelian variety $A$ over a number
field $K$ and a prime $\ell$, the representation of $G_K$ on $V_\ell(A)$ is semisimple.
""",
        caveat='',
        src=r"""
G. Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent. Math. 73 (1983),
Satz 3. Locator unverified.
"""),
    'r9b': dict(
        group='heights', slug='faltings-tate-conjecture',
        title="Faltings' theorem on Tate's conjecture",
        anchor='Faltings Tate conjecture',
        statement=r"""
The *Tate statement* is the following assertion. For abelian varieties $A$ and $B$ over a number field
$K$ and a prime $\ell$, the natural map
$\operatorname{Hom}_K(A,B)\otimes\mathbb Z_\ell\to\operatorname{Hom}_{\mathbb Z_\ell}(T_\ell A,T_\ell B)$
is injective, with image the $G_K$-equivariant maps.
""",
        caveat='',
        src=r"""
G. Faltings, Invent. Math. 73 (1983), Satz 4 (the case $A=B$) and Korollar 1 (Tate's conjecture).
Locators unverified.
"""),
    'bostLowerBound': dict(
        group='heights', slug='bost-lower-bound',
        title="Bost's lower bound for the Faltings height",
        anchor='Bost lower bound',
        statement=r"""
The *Bost statement* is the following assertion. For an abelian variety $A$ of dimension $g$ over a
number field, with stable Faltings height $h_F(A)$,
$$h_F(A)+\tfrac g2\log\pi\;\ge\;-\tfrac g2\log(2\pi),$$
that is, $h_D(A)\ge-\frac g2\log(2\pi)$.
""",
        caveat=r"""
The displayed constant of Bost's bound has not been read: the statement takes the weaker of the two
usual normalizations, and would be slightly stronger than the print only under a third.
""",
        src=r"""
J.-B. Bost, Sém. Bourbaki 795, Astérisque 237 (1996): $h_D(A)\ge-\frac g2\log2\pi$ in Deligne's
normalization. Display and locator unverified.
"""),
    'javanpeykarBound': dict(
        group='heights', slug='javanpeykar-bound',
        title="Javanpeykar's bound for curves with a Belyi function",
        anchor='Javanpeykar bound',
        statement=r"""
The *Javanpeykar statement* is the following assertion. Let $X$ be an integral curve over a number
field $K$ with a $K$-rational point, $J$ its Jacobian, of dimension $g\ge1$, and $t$ a Belyi function
on $X$ over $K$ (a rational function unramified outside $0,1,\infty$) of degree $d$. Then
$$h_F(J)\le13\cdot10^6\,g\,d^5.$$
""",
        caveat='',
        src=r"""
A. Javanpeykar, *Polynomial bounds for Arakelov invariants of Belyi curves*, Algebra Number Theory 8
(2014), Theorem 1.1.1, read by the locator audit, for curves over $K$ with a $K$-rational Belyi
function, over the stable height.
"""),
    'pazukiCor13Upper': dict(
        group='heights', slug='pazuki-bound',
        title="Pazuki's comparison of the theta height with the Faltings height",
        anchor='Pazuki bound',
        statement=r"""
The *Pazuki statement* is the following assertion. Let $A$ be an abelian surface over a number field
$K$, $\sigma:K\to\mathbb C$ an embedding, $\Lambda$ the kernel of a uniformization of $A_\sigma$ and
$\Omega\in\mathfrak H_2$ a period matrix of $\Lambda$. Let $z=(z_m)$, indexed by the characteristics of
level $2$, have coordinates in a number field $F\subset\mathbb C$, with $z_m=c\,\theta_m(0,\Omega)$
for all $m$ and some $c\ne0$, and let $h_2(z)$ be its absolute logarithmic height, with the $L^2$ norm
at the archimedean places. Put $a=\max(1,h_2(z))$ and $b=\max(1,h_F(A)+\log\pi)$. Then
$$a-\tfrac b2\le C_2\log\bigl(\min(a,b)+2\bigr),\qquad C_2=1000\cdot2^4(\log2^4)^5.$$
""",
        caveat=r"""
It is the upper half of the printed corollary. If the level-$2$ theta coordinates in Pazuki's paper
are the second-order ones, this statement is about $\log4$ stronger than the print, and whether the
argument tolerates the weaker constant has not been checked.
""",
        src=r"""
F. Pazuki, *Theta height and Faltings height*, Bull. SMF 140 (2012), Corollary 1.3(2), upper half,
read by the locator audit. The level-$2$ coordinates are a risk (project note height-split, §8).
"""),
    'gaudronRemondThm14': dict(
        group='heights', slug='gaudron-remond-isogeny-bound',
        title='The isogeny theorem of Gaudron and Rémond',
        anchor='Gaudron-Remond isogeny bound',
        statement=r"""
The *isogeny statement* is the following assertion. Let $A$ and $B$ be isogenous abelian varieties
over a number field $K$ of degree $d$, with $\dim A=g$. Then there are isogenies $A\to B$ and $B\to A$
of degree at most
$$\kappa=\Bigl((14g)^{64g^2}\,d\,\max\bigl(h_F(A),\log d,1\bigr)^2\Bigr)^{1024g^3}.$$
""",
        caveat='',
        src=r"""
É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), Theorem 1.4, read by
the locator audit, over the stable height.
"""),
    # ----- p-adic-hodge -----
    'tateTwistInvariants': dict(
        group='p-adic-hodge', slug='invariants-of-tate-twists',
        title="Tate's theorem on the invariants of the twists of C_p",
        anchor='Tate twists',
        statement=r"""
The *twist statement* is the following assertion. For a finite extension $K$ of $\mathbb Q_p$ in
$\overline{\mathbb Q}_p$ and an integer $i\ne0$, $\mathbb C_p(i)^{G_K}=0$.
""",
        caveat=r"""
Tate proves it for every complete discretely valued field of characteristic $0$ with perfect residue
field of characteristic $p$.
""",
        src=r"""
J. Tate, *$p$-divisible groups*, Proc. Conf. Local Fields (Driebergen 1966), Springer (1967),
158–183, §3.3, Theorem 2. Locator unverified.
"""),
    'axSenTate': dict(
        group='p-adic-hodge', slug='ax-sen-tate',
        title='The Ax–Sen–Tate theorem',
        anchor='Ax-Sen-Tate',
        statement=r"""
The *Ax–Sen–Tate statement* is the following assertion. For a finite extension $K$ of $\mathbb Q_p$ in
$\overline{\mathbb Q}_p$, $\mathbb C_p^{G_K}=K$.
""",
        caveat=r"""
The inclusion $K\subseteq\mathbb C_p^{G_K}$ is trivial; the content is the other inclusion.
""",
        src=r"""
J. Tate (1967), §3.3, Theorem 1; S. Sen, Ann. of Math. 90 (1969); J. Ax, Invent. Math. 10 (1970).
Locators unverified.
"""),
    'hodgeTateDecompAbVar': dict(
        group='p-adic-hodge', slug='hodge-tate-decomposition',
        title='The Hodge–Tate decomposition of an abelian variety',
        anchor='Hodge-Tate decomposition',
        statement=r"""
The *Hodge–Tate statement* is the following assertion. Let $A$ be an abelian variety of dimension $g$
over a finite extension $F$ of $\mathbb Q_p$, and $V_p(A)$ its rational Tate module. Then there is a
$G_F$-equivariant $\mathbb C_p$-linear isomorphism
$$\mathbb C_p\otimes_{\mathbb Q_p}V_p(A)\;\cong\;\mathbb C_p(1)^g\oplus\mathbb C_p^g,$$
where $G_F$ acts on the left by $\sigma\otimes\rho(\sigma)$ and on $\mathbb C_p(1)$ through the
cyclotomic character.
""",
        caveat=r"""
The printed decomposition is
$(\mathbb C_p(1)\otimes_F t_A)\oplus(\mathbb C_p\otimes_F t_{A'}^{*})$, with $t_A$ the tangent space
at the origin and $A'$ the dual; the statement chooses bases of the two $g$-dimensional spaces.
""",
        src=r"""
J.-M. Fontaine, *Formes différentielles et modules de Tate des variétés abéliennes sur les corps
locaux*, Invent. Math. 65 (1982), 379–409, Théorème principal; with J. Tate (1967), §4, Corollary 2 of
Theorem 3, for good reduction, and G. Faltings, J. Amer. Math. Soc. 1 (1988), for étale $H^1$.
Locators unverified.
"""),
    'deRhamH1AbVarT': dict(
        group='p-adic-hodge', slug='de-rham-comparison',
        title='The de Rham comparison for an abelian variety',
        anchor='de Rham comparison',
        statement=r"""
The *de Rham statement* is the following assertion. Let $A$ be an abelian variety over a finite
extension $F$ of $\mathbb Q_p$ and $W=\operatorname{Hom}_{\mathbb Q_p}(V_p(A),\mathbb Q_p)$, with the
contragredient action of $G_F$. Then $W$ is de Rham: $D_{\rm dR}(W)=(B_{\rm dR}\otimes W)^{G_F}$ has
dimension $\dim_{\mathbb Q_p}W$ over $F$.
""",
        caveat=r"""
The literature states it for $H^1_{\rm et}(A_{\overline F},\mathbb Q_p)$, which is identified with
$W$ in the standard way (Milne, *Abelian varieties*, Theorem 15.1(a)).
""",
        src=r"""
G. Faltings (1989); T. Tsuji (1999); P. Scholze, Forum Math. Pi 1 (2013), Corollary 1.8; J.-M.
Fontaine (1982) for abelian varieties. Locators unverified.
"""),
    'r11r12': dict(
        group='p-adic-hodge', slug='pan-fontaine-mazur',
        title="Pan's Fontaine–Mazur theorem, with Berger's theorem",
        anchor='Pan and Berger',
        statement=r"""
The *Fontaine–Mazur statement* is the following assertion. Let $p\ge5$ be a prime and
$\rho:G_{\mathbb Q}\to\mathrm{GL}_2(\overline{\mathbb Q}_p)$ a continuous representation that is
irreducible, ramified at finitely many primes, odd, and de Rham at $p$ with distinct Hodge–Tate
weights. Then there is a normalized eigenform $g$ of some level $N\ge1$ and weight $k\ge1$ such that
$\rho$ is attached to $g$ up to twist by a character, away from a finite set of primes.
""",
        caveat=r"""
It combines Pan's theorem, which asks for $\rho$ potentially semistable at $p$, with Berger's
theorem that de Rham representations are potentially semistable. The manuscript's argument proves that
the representation is de Rham and then applies Berger.
""",
        src=r"""
L. Pan, *The Fontaine–Mazur conjecture in the residually reducible case*, J. Amer. Math. Soc. (2022),
Theorem 1.0.4; L. Berger, Invent. Math. 148 (2002), Theorem 0.7. Locators unverified.
"""),
    # ----- modular-galois -----
    'dsThm965Weak': dict(
        group='modular-galois', slug='deligne-representations',
        title="Deligne's Galois representations of eigenforms",
        anchor='Deligne representations',
        statement=r"""
The *Deligne statement* is the following assertion. Let $\ell$ be a prime and $f\in S_k(N,\chi)$ a
normalized eigenform of weight $k\ge2$. Then there is a continuous representation
$\rho:G_{\mathbb Q}\to\mathrm{GL}_2(\overline{\mathbb Q}_\ell)$ such that for every prime $p\nmid N\ell$:
$\rho$ is unramified at $p$, $a_p(f)$ and $\chi(p)p^{k-1}$ are the images under $\iota_{\mathbb C}$ of
algebraic numbers $\alpha$ and $\beta$, and for every arithmetic Frobenius $\sigma$ at $p$ either the
characteristic polynomial of $\rho(\sigma)$ is $x^2-\iota_\ell(\alpha)x+\iota_\ell(\beta)$ or
$\rho(\sigma)$ satisfies this polynomial.
""",
        caveat=r"""
Diamond and Shurman's theorem gives this under either of its two possible wordings (the characteristic
polynomial, or "satisfies"). That $a_p(f)$ is algebraic rests on their printing the theorem with
the number field $K_f$ of the coefficients, which still needs a page check; the convention by which
the coefficients are carried from $\mathbb C$ to the $\ell$-adic field was flagged for a human check.
""",
        src=r"""
F. Diamond and J. Shurman, *A First Course in Modular Forms*, GTM 228 (2005), Theorem 9.6.5 (P.
Deligne 1971; G. Shimura 1971, Theorem 7.14, for $k=2$), in its weakest reading; coefficients carried
along $\iota_\ell\iota_{\mathbb C}^{-1}$. Numbering unverified.
"""),
    'dsThm966': dict(
        group='modular-galois', slug='deligne-serre',
        title='The Deligne–Serre theorem',
        anchor='Deligne-Serre',
        statement=r"""
The *Deligne–Serre statement* is the following assertion. For a normalized eigenform
$f\in S_1(N,\chi)$ there is a continuous representation $\rho_f:G_{\mathbb Q}\to\mathrm{GL}_2(\mathbb C)$
with finite image, unramified at every prime $p\nmid N$, such that the trace and the determinant of an
arithmetic Frobenius at $p$ are $a_p(f)$ and $\chi(p)$.
""",
        caveat='',
        src=r"""
P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Ann. Sci. ÉNS 7 (1974), Theorem 4.1;
Diamond–Shurman, Theorem 9.6.6. Numbering unverified.
"""),
    'eigenformHTNew': dict(
        group='modular-galois', slug='kato-hodge-tate-weights',
        title='Hodge–Tate weights of the representation of a newform',
        anchor='Kato Hodge-Tate weights',
        statement=r"""
The *Hodge–Tate weight statement* is the following assertion. Let $\ell$ be a prime, $f\in S_k(N,\chi)$
a newform of weight $k\ge2$, and $\rho:G_{\mathbb Q}\to\mathrm{GL}_2(\overline{\mathbb Q}_\ell)$ a
semisimple representation attached to $f$. Then $\rho$ restricted to a decomposition group at $\ell$
has Hodge–Tate weights $0$ and $1-k$.
""",
        caveat=r"""
Kato prints that the representation $V_{F_\lambda}(f)$ he constructs is de Rham at $\ell$ with
Hodge–Tate weights $0$ and $k-1$, in the cohomological normalization. The statement needs, besides,
that every semisimple $\rho$ attached to $f$ is the dual of $V_{F_\lambda}(f)$ (Chebotarev and
Brauer–Nesbitt), and that duals negate Hodge–Tate weights.
""",
        src=r"""
K. Kato, Astérisque 295 (2004), 9.2–9.4, for newforms, transported to every semisimple attached
representation and dualized. Locators unverified.
"""),
    'r16CoreY': dict(
        group='modular-galois', slug='shimura-abelian-varieties',
        title="Shimura's abelian varieties attached to newforms",
        anchor='Shimura abelian varieties',
        statement=r"""
The *Shimura statement* is the following assertion. Let $f\in S_2(\Gamma_1(N))$ be a newform with
character $\chi$, $K_f$ the field generated by its coefficients and $J=J_1(N)$. Then $K_f$ is a number
field, and there are an abelian variety $A$ over $\mathbb Q$ with a surjection $J\to A$ over
$\mathbb Q$ and an embedding $\theta:K_f\to\operatorname{End}^0(A)$, with $\dim A=[K_f:\mathbb Q]$,
such that for every prime $\ell$ and every prime $p\nmid N\ell$ an arithmetic Frobenius at $p$ acts on
each component of $V_\ell(A)$ for an embedding $\iota$ of $K_f$ with trace $\iota(a_p)$ and
determinant $\iota(\chi(p))\,p$.
""",
        caveat=r"""
It combines two printed theorems about Shimura's abelian variety $A_f$: its construction, with the
action of $K_f$ and its dimension, and the characteristic polynomial of Frobenius on its Tate modules,
from the Eichler–Shimura congruence relation. The rank-two clause of Shimura's theorem is proved here
from the torsion and characteristic-polynomial statements.
""",
        src=r"""
G. Shimura, J. Math. Soc. Japan 25 (1973), Theorem 1, unconditional clauses ($A_f$, the action of
$K_f$, $\dim A_f=[K_f:\mathbb Q]$); Diamond–Shurman, Theorem 9.5.4, and G. Shimura, *Introduction to
the arithmetic theory of automorphic functions* (1971), Theorem 7.11 (the characteristic polynomial of
Frobenius on $V_\ell(A_f)$, from the congruence relation, Theorem 7.9). Numbers unverified.
"""),
    'r17': dict(
        group='modular-galois', slug='carayol-conductor',
        title="Carayol's theorem on the conductor",
        anchor='Carayol conductor',
        statement=r"""
The *Carayol statement* is the following assertion. Let $\ell$ be a prime, $f$ a newform of weight $2$
and level $N$ with character $\chi$, and
$\rho:G_{\mathbb Q}\to\mathrm{GL}_2(\overline{\mathbb Q}_\ell)$ a semisimple representation attached to
$f$. Then for every prime $p\ne\ell$ the exponent of the conductor of $\rho$ restricted to a
decomposition group at $p$ is $v_p(N)$.
""",
        caveat=r"""
Carayol's theorem covers every $\ell$, including $2$, and every $p\ne\ell$, including $p\mid N$. The
conductor is the Serre–Tate conductor, which does not change under duals, so the normalization of
the attached representation does not matter. Reaching the statement from the print, for every
semisimple attached representation, takes standard steps.
""",
        src=r"""
H. Carayol, *Sur les représentations $\ell$-adiques associées aux formes modulaires de Hilbert*, Ann.
Sci. ÉNS 19 (1986), Théorème (A), read by the locator audit.
"""),
    # ----- glue -----
    'nvLocalInertia': dict(
        group=None, slug='local-inertia-of-tame-covers',
        title='Local inertia of tame covers of the line',
        anchor='Local inertia of tame covers',
        statement=r"""
The *local inertia statement* is the following assertion. Let $p$ be a prime and $E$ a finite Galois
extension of $\mathbb Q(X)$ of degree less than $p$ whose finite branch points lie in a set $S$ of
rational numbers that are $p$-integral and distinct modulo $p$. Let $b\in S$ be a branch point such
that the residue fields of $E$ above $X-b$ are unramified at $p$. Then every element of an inertia
group at a prime of $E$ above $p\mathbb Z[X]$ is conjugate to an element of an inertia group above
$X-b$.
""",
        caveat=r"""
It is the third step of the project's Lemma NV, through which the proof obtains an unramified vertical
prime above each prime $p>324$ in the Hecke cover. A sketch derives it from Abhyankar's lemma along a
divisor with normal crossings (SGA 1 XIII 5.3), which is proved here only over a discrete valuation
ring, and from Zariski–Nagata purity, which is proved here in dimension $2$; the derivation is not yet
part of the proof.
""",
        src=r"""
The project-authored note `docs/research/h-b1.md`, §3, Lemma NV, step 3, with the notes
`docs/research/sgr-direct.md` and `docs/research/sgr-fold.md`: a consequence of Abhyankar's lemma
(SGA 1 XIII 5.3) and Zariski–Nagata purity (SGA 1 X 3.1), locators unverified. No published statement
has this form.
"""),
}
