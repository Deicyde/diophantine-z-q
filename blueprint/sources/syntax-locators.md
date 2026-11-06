# Locators for the finite specification chapter

Line ranges refer to `diophantine_zq.tex` in this repository (the 11/5 manuscript, SHA-256
`cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`). TeX labels are given
where the item has one. The saved specification and its generators are project-authored
artifacts; they are listed last and serve as cross-checks of the construction, not as
inputs to the proof.

## Input B

Section 1 (`sec:main`), lines 105-107: the input B of Lemma 1.2 (`lem:assembly`). The
templates, fixed constructors and private witness substitutions specify one expression
$P_*$, to which the quantitative syntax calculation applies. Lines 135-137 (proof of
Theorem 1.1) assign B to Sections 2 and 12 and Appendix C.

## Section 2 opening

Section 2 (`sec:syntax`), lines 141-164: the specification has 23 library templates and
seven recipes; the root recipe is `integers`, whose only parameter is the rational
variable at index zero; every other variable is existentially quantified over
$\mathbb Q$. Provenance normalization of the saved file (three diagnostic fields).

## Section 2.1 literal operations

Section 2.1, lines 166-188: scalar nodes, calls with private consecutive witness blocks,
shared nodes, recipes as sums of squares or products; the equivalences
$\sum f_i^2=0\iff\bigwedge f_i=0$ and $\prod f_i=0\iff\bigvee f_i=0$ over $\mathbb Q$
(lines 172-176); private blocks moved to the front and arbitrary values in inactive
product blocks (lines 177-180); rational constants $p/q$ by a fresh $c$ and the global
equation $qc=p$, with $8g_0=1641$, $4g_1=-15465$, $32g_2=87483$ (lines 180-187);
inverses as equations $uv=1$ (lines 187-188).

## Section 2.1 positivity and absolute value

Section 2.1, lines 190-201: $s>0\iff\exists z_1,\dots,z_4\in\mathbb Q,\ s\sum z_i^2=1$,
with the four-square proof sketch (lines 195-197), and
$a=|x|\iff\exists z_1,\dots,z_4,\ a=\sum z_i^2,\ a^2=x^2$ (lines 197-201).

## Section 2.2 fixed constructors

Section 2.2, lines 203-208: the three constructor node types `fixed_integer`,
`psi_component` and `finite_guard_product`.

## Section 2.2 division polynomials

Section 2.2, lines 210-236: the normalized division polynomials $f_n$ on $y^2=x^3+Ax$,
$\psi_n=f_n$ ($n$ odd), $\psi_n=2yf_n$ ($n$ even), the bases $f_0,\dots,f_4$, the even
and odd recurrences, $\psi_{-n}=-\psi_n$; the citation of Sutherland §§5.5-5.6
(Lemmas 5.20, 5.24, Theorem 5.21); $x([n]P)=\phi_n/\psi_n^2$, $y([n]P)=\omega_n/\psi_n^3$,
$\omega_n=(\psi_{n+2}\psi_{n-1}^2-\psi_{n-2}\psi_{n+1}^2)/(4y)$, $\psi_{2n}=2\psi_n\omega_n$;
the fixed-scalar ordinate equation $2y([n]P)\psi_n(P)^4=\psi_{2n}(P)$ and the
nonvanishing of $\psi_n(P)$ on the torsion-free carrier (lines 233-236).

## Section 2.2 catalogue and formal multiple

Section 2.2, lines 238-252: the prime catalogue (first 22 primes above 324 in each unit
class modulo $W=4\prod_{p\le324}p$), $N_s=(\prod_{p\le324}p)H_{\rm cat}$, the least
formal multiple $M_0$ (least $m\ge1$ with $N_s^4\mid a,b$ and $\gcd(c,N_s)=1$ for
$1/x([m]P_0)=(a+bs)/c$ normalized), and the remark that the guard is a finite integer
polynomial whose arithmetic zero set is a separate issue.

## Section 3 point codes

Section 3 (`sec:model`), lines 254-266: $K_0=\mathbb Q(s)$, $s^2=2$, $d=75-53s$,
$E:y^2=x^3-d^2x$, the point $P_0$, the codes $(1,0,0,0,0)$ and $(0,x_0,x_1,y_0,y_1)$,
and $\iota(n)$, the code of $[n]P_0$.

## Section 3.1 membership and natural codes

Section 3.1, lines 350-374: the membership equations, the raw-addition contract, and
the natural predicate (four multiplication calls and three additions, Lagrange's
theorem).

## Section 6 multiplication template

Section 6 (`sec:mult`), lines 1123-1224: the multiplication template with 35,134
witnesses, the formal logarithm $L$, the twelve tests of a test group, the slope
predicate, and the height certificate.

## Section 10 translation

Section 10.4, lines 6052-6093: the typing order of the templates, the power-value recipe
(three signed code inputs, seventy-nine private natural witnesses, root equality
$[17751579,15]$), the precision parent (54,056 explicit variables, 15,845 private blocks
of seventy-nine variables), and the remark that equality is a difference, conjunction a
sum of squares and disjunction a product, including the globally conjoined fixed
equations.

## Section 12.2 syntax bounds

Section 12.2, lines 6362-6441: the quantitative syntax calculation; the counts 173
scalar constant nodes and 50 finite constructors (lines 6372-6379); the root recipe
declares $292\,890\,231\,904$ witnesses (lines 6438-6439).

## Appendix C opening

Appendix C (`app:literal`), lines 6666-6682: the root `integers`; variable zero is the
input and variables $1,\dots,292890231904$ its witnesses; point references $r\ge0$,
$-1$, $-2$, $-3$; the three generator constraints conjoined by every model recipe.

## Appendix C.1 scalar nodes

Appendix C.1, lines 6683-6721: node semantics in stored topological order; calls
(substitute the parameter polynomials for variables $0,\dots,p-1$ and $X_{w+j}$ for
variable $p+j$); `fixed_integer` and its operators (literals, references, addition,
multiplication, powers, maximum, factorial, catalogue product and maximum, least formal
multiple); `psi_component` with pair multiplication and $A=(-11243,7950)$; the fixed
point codes $x_n$, $y_n$; `finite_guard_product` over $[-T,T]^3$ with $ab\ne c$ and the
factor $\sum_{j=1}^{15}(DX_j-(D/B_j)A_j)^2$.

## Appendix C.2 recipes and counts

Appendix C.2, lines 6722-6782: constraints of a model-evaluation recipe; composition
recipes (sum of squares, product); parameters `[var,i]`; disjoint private blocks; the
table of the 23 templates (parameters, witnesses, root node) and the table of the seven
recipes (parameters, witnesses, total variables); the five scalar-constant templates and
the byte-for-byte retention of large program literals.

## Saved specification

Project artifact `construction/ordinary-integer-definition.json` (23,179,783 bytes, SHA-256
`4d639d4c44e69ea360d36d4591b8fdc82269d68b9363af0157d1e5c1174c7af6`), keys `definitions`,
`library.templates`, `library.fixedConstants`, `library.finitePolynomialConstructors`,
`recipes`; generated by `construction/ordinary-integer-polynomial.js` from
`construction/precision-natural-polynomial.json` (SHA-256
`f3e163f5c60b972c98b48647274f956dd7d78428e27ddc0543574a5f18120b8c`) with the template
generators `rational-elliptic-core.js`, `multiplication-certificate.js`,
`finite-polynomial-expressions.js`, `rational-model-assembly.js`,
`variable-shift-polynomial-library.js`, `elliptic-division-polynomials.js`,
`fixed-certificate-constants.js` and the translator `rational-circuit-translator.js`.
The construction in this chapter mirrors these generators; the saved file is compared
with it by an external script and is not an input to the proof.
