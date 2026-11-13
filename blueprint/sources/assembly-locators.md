# Locators for the assembly chapter

Line ranges refer to `diophantine_zq.tex` in this repository (the 11/5 manuscript, SHA-256
`cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`). TeX labels are given
where the item has one. The saved specification and its generators are project-authored
artifacts; they are listed last and serve as cross-checks of the construction, not as
inputs to the proof.

## Lemma 1.2

`lem:assembly`, Section 1 (`sec:main`), lines 93-121: the six inputs G, M, H, PC, C, B
(lines 93-108), the statement "Assume G, M, H, PC, C, B. Then $P_*$ satisfies
Theorem 1.1" (lines 110-113) and its three-sentence proof (lines 114-121): Section 11 gives
the exact ordinary-value relation with one shared shift and disjoint private witness
blocks, the literal substitutions of B identify the existential polynomial with $P_*$,
and Section 12 gives the bounds.

## Theorem 1.1 proof

Section 1, lines 60-76 (`thm:target`) and 123-140 (proof of Theorem 1.1): the
assignment of G to Section 3 and Proposition 3.1, H to Theorem 4.1, PC to Sections 5 and
7-9, M to Section 6, C to Section 10 and B to Sections 2, 12 and Appendix C.

## Section 2.1 literal operations

Section 2.1, lines 166-201: calls with private witness blocks, sums of squares and
products over $\mathbb Q$, inactive product blocks, rational constants by global
equations ($8g_0=1641$, $4g_1=-15465$, $32g_2=87483$), inverses as equations $uv=1$,
positivity and absolute value by four squares.

## Section 3 codes

`sec:model`, Section 3, lines 254-266: $K_0$, $d=75-53s$, $E$, $P_0$, the codes of points
and $\iota(n)$, the code of $[n]P_0$.

## Section 3.1 natural codes

Section 3.1, lines 350-371: membership in $2E(K_0)$, the raw addition contract
$\operatorname{Add}_{\rm raw}(\iota(a),\iota(b),R)\iff R=\iota(a+b)$, and (lines 366-371) the
natural predicate: four untyped tuples are typed by multiplication calls before their
squares are added, and Lagrange's theorem gives exactly $\iota(\mathbb N)$, using
multiplication completeness.

## Section 4 height constants

`sec:height`, Section 4, lines 377-403: $\mathcal C$, $F(u)$, $M_S(u)$ and the constants
$F_0,D,G_0,E_0,Q_R,B_{\rm cm},C_{\rm cm},H_6(S;R)$, with $H_6(S)=H_6(S;\max(D,\max S,10^{12}))$;
Theorem 4.1 (`thm:height`), lines 404-409. Lines 968-971: the final value argument uses
$S_{\rm ht}=\{p:p\le324\}$.

## Lemma 5.1

`lem:pole`, Section 5, lines 973-1000: the pole polynomial (lines 974-987) and the
one-sided obstruction: if $B\ne0$ and $\Phi(B)$, then $v_p(B)$ is not negative and odd for
any $p\notin S_0=\{2,3,5,7,13\}$.

## Theorem 5.2

`hyp:PC`, Section 5, lines 1001-1003: pole completeness.

## Section 6 formal conventions

Section 6 (`sec:mult`), lines 1131-1150: the conventions $z=-x/y$, $w=1/x$ with $w(O)=0$,
$v(w)=2v(z)$, the formal logarithm and $v(z([n]Q))=v(z(Q))+v(n)$ in the formal
neighbourhood, citing Silverman IV.5.5, IV.6.3-6.4 and VII.2.1-2.2.

## Section 10 precision predicate

`sec:compiler`, Section 10, lines 5746-5789: the signed encoding
$\operatorname{enc}(n)=2n$ $(n\ge0)$, $-2n-1$ $(n<0)$; the input order $(n,\kappa,a,l,j)$; the
early rejections unless $n\notin\mathcal C$, $\kappa\ne0$, $a,l\ge1$, $j=na$; $z=-x/y$,
$z([l]P_0)=u_l+v_ls$, $\epsilon_l=|u_l|+|v_l|$,
$r(a,j)=\tfrac12\operatorname{Tr}_{K_0/\mathbb Q}(z([j]P_0)/z([a]P_0))$; the constant
$A^{(0)}_{\rm ht}=H_6(S_{\rm ht})$ and the final tests $|r(a,j)-n|<\epsilon_l$,
$4\epsilon_l<4^{-A^{(0)}_{\rm ht}|\kappa F(n)|^{24}}$ (lines 5758-5763).

## Section 10.4 translation

Section 10.4, lines 6052-6093: the typing order (membership, raw addition on canonical
inputs, multiplication, then natural codes), the signed-encoding and exceptional branches
starting their addition chains at the natural code, the literal origin or the fixed signed
generator, and the generator equations outside internal products.

## Section 11 opening

`sec:bridge`, Section 11, lines 6094-6101: the ordinary-value deduction from the exact
index model, the compiled precision relation, the height theorem and PC; codes are
capital letters, indices lower case; $t$ is any rational number.

## Section 11.1 approximation

Section 11.1, lines 6102-6129: the relation $\operatorname{Close}(N,\mathcal K,t)$ (choose
$A,L,J$, link the five signed codes to precision inputs in the order $(n,\kappa,a,l,j)$,
impose $|t-r(a,j)|<\epsilon_l$), $B(n,\kappa)=H_6(S_{\rm ht})|\kappa F(n)|^{24}$, the
soundness (`eq:close-sound`, line 6112) and completeness (`eq:close-complete`, line 6114)
of Close, and their proofs (lines 6116-6129): $|t-n|<2\epsilon_l<4^{-B}/2<e^{-B}$; positive
multiples of $P_0$ approach the identity in $E(\mathbf R)\times E(\mathbf R)$; the derivative of
$[n]$ at the identity is $n$ (Silverman IV.2.3(a)).

## Section 11.2 six local tests

Section 11.2, lines 6130-6150: the points $H,U,V_0=H-\mathcal K,V_1=U-\iota(\kappa n)$, the
guards $\kappa\ne0$, $H,V_0\ne O$, $w(Q)=1/x(Q)$, the six tests $D_1,\dots,D_6$, the
quantities $\eta,q,R_0,a_0,R,C_j,W,\Theta,B_{\rm pole}$ and the relation
$\operatorname{Test}(N,\mathcal K,t)$.

## Lemma 11.1

`lem:test`, lines 6151-6201: if $\operatorname{Test}(\iota(n),\iota(\kappa),t)$ holds, then
$M_{S_{\rm ht}}(t)\mid\kappa F(n)$; the proof uses Lemma 5.1, the formal groups at the places
above $p$ and Silverman IV.5.5 and IV.6.4.

## Lemma 11.2

`lem:test-complete`, lines 6202-6235: for every $n\in\mathbb Z\setminus\mathcal C$ there is
$\kappa\ne0$ with $\operatorname{Test}(\iota(n),\iota(\kappa),n)$; the proof uses Silverman VII.6.3,
the choices $H=[2\kappa]P_0$, $U=[2\kappa n]P_0$, $V_0=[\kappa]P_0$, $V_1=[\kappa n]P_0$, a rational
$q$ close to $1/\sqrt{R_0}$ and Theorem 5.2.

## Section 11.3 exact ordinary value

Section 11.3, lines 6236-6271: the relation $\operatorname{Val}(N,t)$, the height bound
$h(t)\le B(n,\kappa)$ in an accepting main branch, the separation
$|t-n|\ge1/b\ge e^{-h(t)}$, completeness with disjoint private blocks, and the
identification of the polynomial (S01, S16) with the saved root $P_*$.

## Section 12 size

`sec:size`, Section 12, lines 6272-6442: the cutoff (Proposition 12.1, `prop:cutoff`) and
the quantitative syntax bounds for $P_*$, which complete the bounds of Theorem 1.1.

## Section 13 scope

Section 13, lines 6443-6465: the table of inputs of Theorem 1.1, listing "Ordinary value:
shared-shift Close and Test, height and rational separation, Section 11".

## Silverman

J. H. Silverman, *The arithmetic of elliptic curves*, second edition, Springer, 2009
(manuscript bibliography, line 11144). Cited in Section 11 for IV.2.3(a) (the derivative
of $[n]$ on the formal group, line 6125), IV.5.5 and IV.6.4 (the formal logarithm, line
6186) and VII.6.3 (finite index of formal neighbourhoods, line 6210); VII.2.1 (reduction)
is cited in Section 12, line 6322.

## Saved specification outer recipes

Project-authored artifacts, cross-checks only. `construction/ordinary-integer-polynomial.js`,
lines 55-84: the composition recipes `close` (line 57), `main` (66), `value_union` (71,
a product, line 76), `value` (77) and `integers` (81), and the precision input order
`n_code, kappa_code, a_code, ell_code, j_code`. `construction/variable-shift-polynomial-library.js`,
lines 12-77: the templates `value.signed_encode` (16), `value.abs` (26),
`value.close_coordinates` (31), `value.test` (43) and `value.exceptions` (70). The saved
`construction/ordinary-integer-definition.json` records the same recipes with parameter
counts $11,6,6,6,1$ and witness counts $292890196199$, $292890231486$, $292890231892$,
$292890231899$, $292890231904$.
