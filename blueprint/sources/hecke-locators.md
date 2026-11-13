# Locators for the Hecke section

The proofs of Hecke's continuation and of the functional equation follow the project-authored notes
`docs/research/bp-hecke-fe.md` (the route through theta series of $\mathbb Z[i]$, Deuring's identity
and the Fourier identity, reduced to Gauss's point count), `docs/research/gauss-proof.md` (Gauss's
point count through a quartic Jacobi sum), `docs/research/hecke-all.md` (the extension of Hecke's
continuation to every $d\ne0$) and `docs/research/contrib-tidy.md` (the layout of the contributed
proofs). These are notes written for this project by AI agents, not published sources. No human has reviewed the notes or the proofs; the proofs are
machine-checked. None of the
original sources below was read for this section: the classical results are cited from memory in
those notes, with section numbers marked unverified there, and the further locators given here are
also from memory and were not checked against the books. Nothing in the section depends on them,
since every step is proved; they say where the arguments are classical.

## The Hecke section

`docs/research/bp-hecke-fe.md` §0 and §2: the plan. Both statements follow from Gauss's point count
on $y^2=x^3-x$ alone; Deuring's identity is stated over the coefficients of the standard Euler
product of $C_d$ and over explicit sums in $\mathbb Z^2$; the functional equation is proved for the
completed twist directly from the Mellin transforms of the theta kernels, without a theta-level
identity. The same note records numerical checks with PARI (VERIFIED there): Deuring's identity for
$d\in\{1,5,13,21,29,37,53,85\}$ and $n\le400$, and the Fourier identity for $d\in\{5,13,21\}$, with
conductors and root numbers from PARI. `docs/research/gauss-proof.md`: the proof of Gauss's point
count, and the consequence that the target follows from the three remaining hypotheses, the minimal
height hypothesis, reading A and Gross–Zagier, which stay unproved: the first is unrefereed and its
new arguments have been reviewed only by AI models, and no refereed text found states reading A
(see [reading A](rank-locators.md#reading-a-of-tian-yuan-zhang)). `docs/research/hecke-all.md`: Hecke's continuation for every $d\ne0$, through the
quadratic twist, the minimality of $y^2=x^3-d^2x$ at $2$ for even squarefree $d$, and the removal of
square factors.

## Theta series and the method of Hecke

The entire continuation and the functional equation of the L-series of a Hecke character, by the
Mellin transform of a theta series and its transformation law under $x\mapsto1/x$, are Hecke's:
E. Hecke, *Eine neue Art von Zetafunktionen und ihre Beziehungen zur Verteilung der Primzahlen*,
Math. Z. 1 (1918), 357–376, and Zweite Mitteilung, Math. Z. 6 (1920), 11–51 (not read). Textbook
accounts: J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer (1999), Chapter VII
(theta series of number fields and Hecke L-series; not checked); N. Koblitz, *Introduction to
Elliptic Curves and Modular Forms*, 2nd ed., Graduate Texts in Mathematics 97, Springer (1993),
Chapter II (the L-function of $y^2=x^3-n^2x$ and its functional equation; not checked, and also cited
under the L-series of the congruent number curves in `rank-locators.md`). The one-variable theta
transformation laws (Poisson summation), the decay of the kernels, and the general theorem on Mellin
transforms of a pair $f(1/x)=\varepsilon x^kg(x)$ are standard and are proved, not
assumed.

## Arithmetic of the Gaussian integers

$\mathbb Z[i]$ is Euclidean, hence a unique factorization domain; its units are $\pm1,\pm i$; an
element of prime norm is prime; a prime $p\equiv1\pmod4$ is a sum of two squares and splits as
$\pi\bar\pi$ with $\pi,\bar\pi$ not associate; a prime $p\equiv3\pmod4$ stays prime. K. Ireland,
M. Rosen, *A Classical Introduction to Modern Number Theory*, 2nd ed., Graduate Texts in Mathematics
84, Springer (1990), Chapter 1 and Chapter 9 (not checked). All of these facts are proved, not assumed; the
basic ones (Euclidean, units, sums of two squares, inert primes) come from the general library the
proofs build on.

## Gauss and Jacobi sums

Quadratic Gauss sums, $g^2=\left(\frac{-1}p\right)p$, Jacobi sums of characters of $\mathbb F_p$
and $J(\chi,\varphi)J(\bar\chi,\bar\varphi)=p$, and the congruence of the quartic Jacobi sum modulo
$2+2i$: Ireland–Rosen, Chapter 6 (quadratic Gauss sums; not checked), Chapter 8 (Gauss and Jacobi
sums) and Chapter 9 §9 (the congruence), the last two cited in `docs/research/gauss-proof.md` with
section numbers from memory (UNVERIFIED there). The two-dimensional quadratic Gauss sum
$\sum_{x,y}\chi(x^2+y^2)e((xn_1+yn_2)/p)=p\,\chi(n_1^2+n_2^2)$ and the factorization of the Fourier
transform of the Hecke character into a 2-part and an odd part follow `docs/research/bp-hecke-fe.md`
§2.4, where both are also checked numerically. The congruence modulo $2+2i$ is proved here directly,
by pairing $t$ with $t^{-1}$, not taken from the book.

## The point count of Gauss

For a prime $p\equiv1\pmod4$, the number of solutions of $y^2=x^3-x$ over $\mathbb F_p$ is $p+2A$,
where $p=A^2+B^2$ and $-(A+Bi)\equiv1\pmod{2+2i}$. The project notes attribute it to Gauss (1814) and
cite Ireland–Rosen, Chapter 18 §4, for the count (`docs/research/gauss-proof.md`,
`docs/research/bp-hecke-fe.md` §0, `docs/research/hecke-all.md`; section number from memory,
UNVERIFIED there; Gauss's own text was not read). `docs/research/pd-paper.md` records the same fact as
the classical evaluation of the Frobenius of $y^2=x^3-x$, with Silverman's *The Arithmetic of
Elliptic Curves*, III.7.4, III.8.6 and V.2.3.1 as cited in the manuscript (not checked here).

## Deuring and the Hecke character

$C_d$ has complex multiplication by $\mathbb Z[i]$, and its L-series is that of the Hecke character
$\psi_d(\alpha)=\left(\frac{N(\alpha)}d\right)u(\alpha)\alpha$ of $\mathbb Q(i)$, of infinity type
$z\mapsto z$ and conductor $(2+2i)d$ for odd squarefree $d\equiv1\pmod4$ (as stated in `docs/research/bp-hecke-fe.md` §2.1): M. Deuring, *Die Zetafunktion einer algebraischen
Kurve vom Geschlechte Eins*, Nachr. Akad. Wiss. Göttingen, Math.-Phys. Kl. (1953), with continuations
in the same journal (1955, 1956, 1957) (not read); J. H. Silverman, *Advanced Topics in the
Arithmetic of Elliptic Curves*, Graduate Texts in Mathematics 151, Springer (1994), Chapter II (the
L-series of a curve with complex multiplication; not checked). The explicit form used here, with the
primary unit $u(\alpha)$ read off $\alpha$ modulo $4$ and the Jacobi symbol of the norm, is that of
`docs/research/bp-hecke-fe.md` §2.1, which states it for squarefree $d\equiv1\pmod4$ and checks it numerically;
Deuring's identity is neither claimed nor proved here for other $d$, which the section reaches
through the quadratic twist of $C_1$ instead. See also
the section on Hecke and Deuring in `rank-locators.md`.

## The curves for even and non-squarefree d

For even squarefree $d$ the equation $y^2=x^3-d^2x$ is minimal at $2$ by a $c_4$ argument: an
integral equation over $\mathbb Z_2$ has $c_4$ a unit or divisible by $16$, and a change of variables
multiplies $c_4$ by $u^{-4}$ (J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed.,
Springer (2009), §III.1, Table 3.1, and §VII.1, as in `rank-locators.md` under minimal equations;
the $c_4$ argument itself follows `docs/research/hecke-all.md` and is proved here). The L-series is
an isomorphism invariant when $j$ is integral, and $C_{m^2d}\cong C_d$ by
$(x,y)\mapsto(x/m^2,y/m^3)$. The coefficients of $C_d$ are those of $C_1$ twisted by the
Jacobi symbol $\left(\frac dn\right)$, by the substitution $x\mapsto dx$
(`docs/research/hecke-all.md`).
