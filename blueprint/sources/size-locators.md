# Locators for the size chapter

Line ranges refer to `diophantine_zq.tex` in this repository (the 11/5 manuscript, SHA-256
`cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`). TeX labels are given
where the item has one. The companion size proof, the height traversal and the saved
specification are project-authored artifacts; they are listed last and serve as
cross-checks, not as inputs to the proof.

## Section 4 constants

Section 4 (`sec:height`), lines 377-403: the contact set, $M_S(u)$, and the constants
$F_0=324!$, $D=F_0\,3^{256F_0^4}$, $G_0=116064000000$, $E_0=10(DG_0)^2$, $Q_R=R^{RE_0}$,
$B_{\rm cm}=D^2\,3^{21000D^2}+1$, $C_{\rm cm}=2B_{\rm cm}+4096(1028+5D+84000D^2)$ and
$H_6(S;R)=2\cdot10^{13}\max(1,C_{\rm cm},Q_R^{17})$ for $R\ge\max(D,\max S,10^{12})$.

## Section 2.2 catalogue and formal multiple

Section 2.2, lines 238-252: the prime catalogue (first 22 primes above 324 in each unit
residue class modulo $W=4\prod_{p\le324}p$), $N_s=(\prod_{p\le324}p)H_{\rm cat}$, inverse
abscissa zero at the identity, and the least formal multiple $M_0$, "with a successful
index bounded in Section 12" (lines 246-247).

## Section 12 opening

Section 12 (`sec:size`), lines 6272-6283: the literal constants $H_{\rm cat}$, $H_{\max}$,
$N_s=P_sH_{\rm cat}$, $M_0$, $c_*=4M_0$, $R=\max(D,H_{\max},c_*,10^{12})$,
$A_{\rm ht}=2\cdot10^{13}\max(1,C_{\rm cm},Q_R^{17})$, $T=(48A_{\rm ht})^{13}$ and the
pole clearing constant $\ell_0=12P_s^{2916}H_{\rm cat}^{732}$.

## Proposition 12.1

Proposition 12.1 (`prop:cutoff`, "Literal cutoff"), lines 6285-6293:
$R=D$ and $T=(96\cdot10^{13})^{13}D^{2210G_0^2D^3}<2^{2^{2^{9013}}}$.

## Proof of Proposition 12.1, catalogue

Proof of Proposition 12.1, lines 6294-6309: $10^5<W<2^{512}$ and
$2^{2000}<F_0<2^{2250}$ (line 6296); the progression estimate of Bennett, Martin,
O'Bryant and Rechnitzer at $X=2^{W^3}$ (lines 6297-6302); more than 22 primes in each unit
class, none at most 324 (lines 6303-6305); $H_{\max}<X$, $H_{\rm cat}\le X^{22W}$,
$\log_2N_s<2^{2054}$ (lines 6306-6309).

## Proof of Proposition 12.1, formal multiple

Proof of Proposition 12.1, lines 6310-6350: the product $m_0$ of the reduction orders of
$P_0$ at the places above the odd primes dividing $N_s$ (lines 6310-6311); the dyadic
formal subgroup and the identity convention (lines 6312-6316); the bad place
$s\equiv3\pmod7$, where $P_0$ reduces to $(2,6)$ on $y^2=x^3$ (lines 6317-6319); the
nonsingular reduction group, citing Silverman VII.2.1 (lines 6320-6322); Hasse's bound at
good places, $(p+1)^2<p^3$, the singular smooth group of order seven, and $m_0\le N_s^6$
(lines 6323-6327); the identity case (line 6328); the odd-place estimate
$v(1/x([N_s^4m_0]P_0))\ge2+8v_p(N_s)$ (lines 6329-6334); the dyadic estimate
$v_s(1/x([N_s^4m_0]P_0))\ge6+16v_2(N_s)$ from $v_s(x(P_0))=-6$, $v_s(y(P_0))=-9$,
$v_s(z)=3>2$ and the logarithm isometry (lines 6335-6341); extraction of the rational
coefficients and $M_0\le N_s^{10}$ (lines 6342-6350).

## Proof of Proposition 12.1, cutoff

Proof of Proposition 12.1, lines 6351-6360: $c_*<2^{2^{2059}}$,
$2^{2^{8008}}<D<2^{2^{9010}}$, $R=D$ (lines 6351-6352); $C_{\rm cm}<2^{50000D^2}$ and
$\log_2Q_D^{17}=170G_0^2D^3\log_2D>50000D^2$, so the maximum is $Q_D^{17}$ (lines 6353-6357);
$G_0<2^{37}$, $E_0<D^3$, $\log_2Q_D<D^5$, $\log_2A_{\rm ht}<D^7$, $\log_2T<D^8<2^{2^{9013}}$
(lines 6358-6359).

## Section 12.1 norms and division polynomials

Section 12.1, lines 6362-6371: the coefficient $\ell^1$ norm and the weighted pair norm
$\|a+bs\|=\|a\|_1+2\|b\|_1$, both submultiplicative; $\deg f_n\le(n+1)^3$,
$\|f_n\|\le2^{100(n+1)^3}$; the exponent slack $4m^3-24m-27\ge9$ ($m\ge3$) of the even
recurrence and at least ten ($m\ge2$) for the odd one.

## Section 12.1 checked facts

Section 12.1, lines 6372-6383: literal fixed constants and division-polynomial indices at
most $T$; root syntax height at most 256; at most $2^{20}$ constraints per model recipe and
terms per composition recipe; 23 templates, seven recipes, 173 scalar constant nodes and
50 finite constructors.

## Section 12.1 constructor bounds

Section 12.1, lines 6385-6394: $B_*=T+1$; coordinates of $\iota(n)$, $|n|\le T$, have
numerators and denominators at most $2^{K_*}$, $K_*=2^{30}(T+1)^3$; at most eight
quadratic-field operations, each taking a height bound $H$ to $3H^4$; at most $8(T+1)^3$
guard factors; each finite constructor has degree at most $B_*^4$ and
$\log_2\max(1,\|\cdot\|_1)\le B_*^8$.

## Section 12.1 syntax heights

Section 12.1, lines 6396-6431: syntax heights of variables, constants, operations,
constructors and calls; the substitution inequalities; degree and logarithmic norm at most
$B_*^{8h}$ at positive height $h$; renaming calls in the outer composition recipes; the
recipe heights $228,233,235,251,252,254,256$; the safe height four for the model
wrappers; $\deg P_*\le(T+1)^{2048}$ and $|[X^\alpha]P_*|\le2^{(T+1)^{2048}}$.

## Section 12.1 final comparison

Section 12.1, lines 6432-6441: $T+1\le U=2^{2^{2^{9013}}}$,
$(T+1)^{2048}\le U^{2048}=2^{2^{2^{9013}+11}}<2^{2^{2^{9014}}}$, $9014<65536=2\uparrow\uparrow4$,
the comparisons with $2\uparrow\uparrow7$ and $2\uparrow\uparrow8$, and the
$292\,890\,231\,904$ declared witnesses of the root recipe.

## Silverman

Bibliography entry `silverman`, lines 11144-11145: J. H. Silverman, *The arithmetic of
elliptic curves*, second edition, Springer, 2009, Chapters IV and VII. Cited in the proof
of Proposition 12.1 as VII.2.1 (reduction on the nonsingular part, p. 188) and V.1.1
(Hasse's bound, p. 138).

## Bennett-Martin-O'Bryant-Rechnitzer

Bibliography entry `bmor`, lines 11111-11114: Bennett, Martin, O'Bryant and Rechnitzer,
*Explicit bounds for primes in arithmetic progressions*, Illinois J. Math. 62 (2018),
Theorem 1.2. Its use in Proposition 12.1 is replaced by the catalogue bound at the cutoff
$2^{W^8}$, proved from an effective Dirichlet theorem in the progressions chapter.

## Companion size proof

Project-authored artifact `construction/z-in-q-polynomial-size-bound-proof.txt` (source
S26 of the manuscript's source map, line 6641): Section 1, the bounds for the three finite
constructors (division polynomials, coordinate heights, guard); Section 2, the composition
bounds and the height rules; Section 3, the simplification of the uniform bound to $T+1$.

## Height traversal

Project-authored artifacts `construction/bound-ordinary-integer-polynomial.py` and its output
`construction/ordinary-integer-polynomial-size-bounds.json`: the height rules applied to the
saved specification, with the 23 template heights, the seven recipe heights and constraint
counts, and root height 256.

## Saved fixed constants

Project-authored artifact `construction/ordinary-integer-definition.json`, entries
`library.fixedConstants` (the eighteen named constants and the five integer constants) and
`library.finitePolynomialConstructors` (the meaning of `fixed_integer`, `psi_component` and
`finite_guard_product`).
