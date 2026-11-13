# Locators for the Rédei chapter

Rédei's formula is not in the manuscript. The plan of its proof is the project-authored research
note `docs/research/redei-plan.md` of this repository, written for this project and not a published
source; the formulas themselves are derived in `docs/research/tyz-5b.md` §2.2. The published works
are cited at the end.

## The target

`docs/research/redei-plan.md` §§1.1–1.2. Tian–Yuan–Zhang's genus class number is
$g(d)=\#(2\mathrm{Cl}(\mathbb Q(\sqrt{-d})))$, the subgroup of squares of the class group of the ring
of integers, not the 2-torsion; the note checked this against the LaTeX source of arXiv:1411.4728v1,
lines 361–366 and 998. The field is modelled as $\mathbb Q[\omega]/(\omega^2+n)$, and the target is
$g(d_B)\equiv g_d(B)\pmod 2$ for nonempty $B$ ($B=\emptyset$ is excluded, since $g(1)=1$ while Rédei's
bit of $\emptyset$ is $0$).

## The hypothesis in class-number form

`docs/research/redei-plan.md` §1.3: the genus sum $T^{\mathrm{Cl}}_{5b}(d)$ with Tian–Yuan–Zhang's
own $g$, the hypothesis CR₃^TYZ_Cl, and the passage from Rédei's formula to $T^{\mathrm{Cl}}_{5b}=T_{5b}$
and CR₃^TYZ_Cl ⇔ CR₃^TYZ (blocks of a set partition are nonempty).

## The chosen route

`docs/research/redei-plan.md` §3.1, route (c): genus characters $\chi_q([\mathfrak a])=(N\mathfrak a/q)$
for the primes $q\mid n$, Dirichlet's theorem for their surjectivity, and the count
$[\mathrm{Cl}:2\mathrm{Cl}]=\#\mathrm{Cl}[2]\le2^{t-1}\le\#\mathrm{im}\,\chi\le[\mathrm{Cl}:2\mathrm{Cl}]$,
in place of Hasse–Minkowski or Legendre's theorem. Two simplifications: only the odd characters are
needed (image all of $\mathbb F_2^r$ for $n\equiv1\pmod4$ and the sum-zero hyperplane for
$n\equiv3\pmod4$), and $\chi_q$ is well defined with integral ideals only, since
$N(\alpha)=\alpha\sigma(\alpha)$ is a square modulo $\mathfrak p_q$.

## Step 1: the field

`docs/research/redei-plan.md` §3.2, step 1: $\mathbb Q(\sqrt{-n})$ as a number field with two
automorphisms, the integrality of $\omega$ and of $\theta=(1+\omega)/2$ for $n\equiv3\pmod4$, the
norm $N(x)=x\sigma(x)\ge0$, $\mathcal O\cap\mathbb Q=\mathbb Z$ and the rational units $\pm1$,
$\sigma\omega=-\omega$.

## Step 2: primes

`docs/research/redei-plan.md` §3.2, step 2: the splitting trichotomy, ramified primes divide $n$ or
are $2$ with $n\equiv1\pmod4$ (residue-field argument with $x=\omega$ and $x=\theta$), the primes of
the discriminant ramify, the ideals $\mathfrak p_p$, $(\omega)=\prod_{p\mid n}\mathfrak p_p$, and
$I\cdot\sigma I=(NI)$.

## Step 3: ambiguous classes

`docs/research/redei-plan.md` §3.2, step 3 (the step (G1)): Hilbert 90 at the integral level
($x\sigma I=yI$ gives $Nx=Ny$, then $\nu=\sigma x(x+y)$), invariant ideals by strong induction on the
norm, the map $\psi$, $\mathrm{im}\,\psi=\mathrm{Cl}[2]$ and $\#\mathrm{Cl}[2]\le2^{t-1}$.

## Step 4: genus characters

`docs/research/redei-plan.md` §3.2, step 4: representatives prime to $q$, the characters $\chi_q$
and their homomorphism property, and $\chi_q(\psi e)=\sum_pR_{qp}e_p$ with $R_{qp}=(p/q)$,
$R_{qq}=((n/q)/q)$, $R_{q2}=(2/q)$, using $[\mathfrak p_q]=\prod_{p\ne q}[\mathfrak p_p]$ from
$(\omega)=\prod\mathfrak p_p$.

## Step 5: Dirichlet's theorem

`docs/research/redei-plan.md` §3.2, step 5: a prime $p\nmid2n$ with $-n$ a square modulo $p$ splits
(it is not inert, since $(m+\omega)(m-\omega)\in p\mathcal O$ and $\sigma$ give $p\mid2m$); the
surjectivity of the genus characters from residues, the Chinese remainder theorem, Dirichlet's
theorem on primes in progressions and Jacobi reciprocity for $(-n/p)=1$.

## Step 6: the 4-rank

`docs/research/redei-plan.md` §3.2, step 6: $\#G^2$ odd iff $G[2]\cap G^2=1$, $\#(G/G^2)=\#G[2]$,
$\mathrm{Cl}^2=\bigcap\ker\chi_q$ by counting, and the 4-rank statement: $g(n)$ is odd iff the kernel
of the Rédei matrix is $\{0,e_n\}$ (Rédei's theorem in its 4-rank-0 form). The statement needs $n>1$:
for $n=1$ the class group is trivial, but the vector at the prime $2$ lies in the kernel of the empty
matrix.

## Step 7: the kernel

`docs/research/redei-plan.md` §3.2, step 7, in the general setting of bits with reciprocity: the
kernel of $(L_B\mid z_B)$ (the column $z_B$ only if $y(B)=0$) is trivial iff Rédei's bit is $1$. This
is tyz-5b §2.2, Cases 1 and 2, with Lemma 2.2(2) and the row- and column-sum facts.

## Step 8: the bridge

`docs/research/redei-plan.md` §3.2, step 8: the primes of $d_B$ are those of $B$,
$d_B\equiv3\pmod4$ iff $y(B)=1$, the Rédei matrix of $d_B$ becomes the Laplacian of the bits of $d$
bordered by $z$, and Rédei's formula follows from the 4-rank statement.

## Redei's formulas

`docs/research/tyz-5b.md` §2.2, Proposition 2.3: for $\emptyset\ne B$ and $d=d_B$,
$g(d)=\kappa(B)$ if $y(B)=1$ and $g(d)=\sum_{\rho\in B}z_\rho\kappa_\rho(B)$ if $y(B)=0$ (the rows
$n\bmod4=3,1$ of Smith's Table 1). The derivation from genus theory there uses (G1) ambiguous
classes, (G2) and (G3) Hasse–Minkowski, and Cases 1 and 2 for the kernel; the Rédei chapter follows
route (c) of redei-plan in place of (G2) and (G3).

## The kernel plan

`KERNEL_PLAN.md`, the paragraph beginning "That step is done": Rédei's formula is proved, so
CR₃^TYZ_Cl, with Tian–Yuan–Zhang's own $g(d)=\#2\mathrm{Cl}(\mathbb Q(\sqrt{-d}))$, is equivalent to
CR₃^TYZ. The next paragraph, beginning "These hypotheses all conclude": CR₃^TYZ_Cl,Rk implies
CR₃^TYZ,Rk, by Rédei's formula.

## Redei 1934

L. Rédei, J. reine angew. Math. 171 (1934), cited by `docs/research/tyz-5b.md` §2.2 for the
classical facts (G1)–(G3) of genus theory. The note marks its exact theorem numbers UNCHECKED, and
they were not checked either. The title, *Arithmetischer Beweis des Satzes über
die Anzahl der durch vier teilbaren Invarianten der absoluten Klassengruppe im quadratischen
Zahlkörper*, and the pages 55–60 were also not checked against the journal.

## Tian-Yuan-Zhang

Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent number problem*, Asian J.
Math. 21 (2017), no. 4, 721–774; arXiv:1411.4728. §1: the genus class numbers
$g(d):=\#(2\mathrm{Cl}(\mathbb Q(\sqrt{-d})))$ and the remark that by Rédei their parity is computed
by the Rédei matrix; Theorem 3.5 and the proof of Theorem 3.5(2) (§3.3) for the hypothesis in
class-number form.

## Cox

D. A. Cox, *Primes of the form $x^2+ny^2$*, §6, as cited by `docs/research/redei-plan.md` §3.1 for
the classical proof that the number of genera is $2^{t-1}$. The section number was not checked. The Rédei chapter obtains the principal genus theorem by counting instead.
