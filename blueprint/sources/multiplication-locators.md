# Locators for the multiplication chapter

Line ranges refer to `diophantine_zq.tex` in this repository (the 11/5 manuscript, SHA-256
`cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`). TeX labels are given
where the item has one. The JavaScript generators under `construction/` are
project-authored artifacts; they are listed last and serve as cross-checks of the shapes and
constants, not as inputs to the proof.

## Multiplication input M

Section 1 (`sec:main`), lines 96-97: the input M of Lemma 1.2: the actual guarded
multiplication template has rational witnesses exactly for triples with indices $a,b,ab$.
Lines 129-131 (proof of Theorem 1.1) assign M to Section 6, on all rational input codes,
including the finite false-triple guard.

## Assembly lemma

`lem:assembly`, Lemma 1.2, lines 110-121: assuming G, M, H, PC, C and B, the specified
polynomial satisfies Theorem 1.1.

## Least formal multiple

Section 2.2, lines 238-252: the fixed prime catalogue, $N_s=(\prod_{p\le324}p)H_{\rm cat}$,
the definition of $M_0$ as the least $m\ge1$ with $N_s^4\mid a,b$ and $\gcd(c,N_s)=1$ for
$1/x([m]P_0)=(a+bs)/c$, and the remark that bounding $T$ does not by itself exclude false
triples.

## Membership and addition

Section 3.1, lines 351-374: membership in $2E(K_0)$ is an all-input statement;
multiplication first imposes membership of its three roots and is sound on arbitrary
rational tuples.

## Contact prime sets

End of Section 4, lines 967-971: $S_{\rm ht}=\{p:p\le324\}$ and
$S_{\rm mul}=S_{\rm ht}\cup\mathcal H\cup\operatorname{supp}(c_*)$, with $\mathcal H$ the
fixed catalogue; a common numerical $R$ may bound both sets.

## Pole predicate

`sec:pole`, Section 5, lines 973-987: $S_0=\{2,3,5,7,13\}$, the eleven witnesses, the
multiplier $m$, $A=mB$, $H=A(A-B^2)$, $T_1$, $T_2$, $Q_{\rm pole}$, $\Phi(B)$; for $B\ne0$,
$m$ is a signed divisor of $2730$ and the equations give points $(A,r_1)\in E_e$ and
$(Az^2,zr_2)\in E_{eH}$ with $eHz\ne0$, where $E_\ell:y^2=x(x-\ell)(x+3\ell)$; total degree
$75$. The blueprint uses the Route K polynomial instead, with the factors $A+e$ and $Az^2+eH$ and
the curves $y^2=x(x-\ell)(x+\ell)$; see the
[Route K locators](route-k-locators.md#soundness-for-the-congruent-number-curves).

## One-sided obstruction

`lem:pole`, Lemma 5.1, lines 988-991, proof lines 992-1000: if $B\ne0$ and $\Phi(B)$, then
$v_p(B)$ is not negative and odd for any $p\notin S_0$.

## Pole completeness

`hyp:PC`, Theorem 5.2, lines 1001-1004. Used here only as the hypothesis of the
completeness direction; for the Route K polynomial it is proved from the certified rank
hypothesis CR₃.

## Section 6 opening

`sec:mult`, Section 6, lines 1123-1129: the template forces membership of its three
inputs inside the height certificate; accepted untyped inputs have unique indices; the
template has $35{,}134$ rational witnesses (construction S03, specification S13).

## Local conventions

Lines 1131-1149: $z=-x/y$, $w=1/x$ with $w(O)=0$, $w=z^2$ times an integral unit; the formal
logarithm converges on $v(z)>0$ and is an isometry on $v(z)>e/(p-1)$ (Silverman IV.5.5,
IV.6.3-6.4); the relative error estimate $(r-1)v(z)-e\,v_p(r)>0$;
$\log([n]Q)=n\log(Q)$ and $v(z([n]Q))=v(z(Q))+v(n)$; identification with the reduction
kernel of a minimal model (Silverman VII.2.1-2.2).

## Logarithm series

Lines 1150-1161: the invariant differential $dx/(2y)=dz/\sqrt{1+4d^2z^4}$, the series
$\log(z)=\sum_j(-1)^j\binom{2j}{j}d^{2j}z^{4j+1}/(4j+1)$, and the estimate: at a contact
prime $p>324$ with $v(z)\ge1$, $v(p)=1$, every omitted term relative to $z$ has valuation
at least $r-1-v_p(r)\ge28$ for $r\ge29$, so $L(z)/16575=\log(z)(1+\epsilon_z)$ with
$v(\epsilon_z)\ge28$.

## Twelve tests

Lines 1162-1176: $H=[h]P_0$, $U_i=[z_i]P_0$, $V_0=H-[c_*]P_0$, $V_i=U_i-[c_*n_i]P_0$,
$c_*=4M_0$; the truncated logarithm $L$; the twelve tests (four inverse abscissas, four
conjugate counterparts, three differences of $L$-ratios, one product test); identity
inverse abscissas are zero and all denominators are guarded.

## Slope predicate

Lines 1177-1192: for a slope $t\notin\mathcal C\cup\{1\}$, $R_0=\eta F(t)/(t-1)^8$,
$\eta^2=1$, $a=1-R_0q^2\ne0$, $R=\ell_0^2a^2R_0$; the normalized values
$C_{gj}=D_{gj}/(R_0^{k_j}(t-1)^{k_j+1})$ with $k_j=1$ ($j\le8$) and $25$ ($j\ge9$); six
groups, $W_g=\prod_j(1+RC_{gj}^2)$, $\Theta=\operatorname{Tr}\sum_gW_g^{-1}$, both nonzero,
and $\Phi(R/\Theta^2)$; the pole input is nonzero.

## Local congruence

Lines 1194-1213: at a positive odd contact prime outside $S_{\rm mul}$, the factor
valuations, the trace and Lemma 5.1 give one common group and place with the first eight
tests of valuation at least one and the last four at least $25$; the formal group, the unit
among $h,h-c_*$, the full-log and truncated ratios, and $p^{25}\mid n_1n_2-n_3$.

## Height certificate

Lines 1215-1223: the abscissas $x_{i0}+x_{i1}s$ (zero at the identity),
$b_ix_{ij}=a_{ij}$ with $b_i\ne0$, each of the nine quantities a sum of three slopes, the
slope predicate on all $27$ slopes, membership of the three inputs; the multiplication
predicate conjoins it with the scalar graphs and the inverse of the guard.

## Finite-box deduction

`prop:box`, Proposition 6.1, lines 1225-1229, proof lines 1230-1246: every false triple
accepted by the unguarded certificate has $\max_i|n_i|<T=(48A_{\rm ht})^{13}$; the
constants $12A_{\rm ht}$, $B_0=4\log3+\tfrac32\log2+2\log(1+\sqrt2)+\tfrac13\log676<10$ and
$2\widehat h(P_0)>1$.

## Finite guard

Lines 1248-1259: the guard factors $g_{abc}$ over false triples in $[-T,T]^3$; a false
accepted triple makes its own factor zero; at a true triple every factor is positive by
injectivity of codes; the sound direction uses the generator and the height theorem but not
pole completeness.

## Prime pattern

`prop:fixed-prime-pattern`, Proposition 6.2, lines 1267-1297 (statement); its proof,
lines 1299-1704, is replaced in this project by the hypothesis 22P.

## Choice of shifts

Lines 1705-1723: the nine integral homogeneous quantities of a true triple; at most six
odd-contact primes per slope; $h\equiv0\pmod{\operatorname{lcm}(M_0,d_1)}$,
$h\equiv c_*\pmod{d_2}$, compatibility via $\gcd(d_1,d_2)=4$; a solution larger than $c_*$;
one private group per contact prime; $U_i=[n_i]H$.

## Fixed local clearing

Lines 1723-1730: $S_b=S_{\rm ht}\cup\mathcal H$, $B_p$, $C_p=14B_p$, $D_p=51C_p$,
$|v_p(R_0)|,|v_p(t-1)|\le C_p$, $v_p(D_{gj})\ge0$ at $S_b$ from the small formal subgroup of
$M_0$, $v_p(C_{gj})\ge-D_p$, $v_p(\ell_0)=E_p=52C_p+v_p(12)+4$.

## Pole input of a completed slope

Lines 1732-1748: weak approximation for $q$; $\eta$ with $R_0>0$; at $S_b$,
$v_p(RC_{gj}^2)\ge2E_p-C_p-2D_p>v_p(12)$ and $v_p(R/\Theta^2)\ge103C_p+8\ge4$; at a selected
odd-contact prime $v_p(R)=1$ and the trace residues; even valuation elsewhere; positivity in
both real embeddings and $R/\Theta^2\to0$ as $a\to0$.

## Conclusion of the multiplication proof

Lines 1748-1754: the hypotheses of PC hold, negative and zero indices and coincident points
are handled by the group-law branches, and M holds, with completeness for every integer
triple $(n_1,n_2,n_1n_2)$ and soundness on arbitrary rational input codes.

## Fixed constants

Section 12 (`sec:size`), lines 6272-6283: $H_{\rm cat}$, $H_{\max}$, $N_s$, $M_0$,
$c_*=4M_0$, $R=\max(D,H_{\max},c_*,10^{12})$,
$A_{\rm ht}=2\cdot10^{13}\max(1,C_{\rm cm},Q_R^{17})$, $T=(48A_{\rm ht})^{13}$, and
$\ell_0=12P_s^{2916}H_{\rm cat}^{732}$.

## Least formal multiple exists

Proof of `prop:cutoff`, Proposition 12.1, lines 6310-6349: the search defining $M_0$
succeeds by $N_s^4m_0$, so $1\le M_0\le N_s^{10}$.

## Generator height

Proof of `prop:generator`, lines 303-325: the duplication bounds on $C$, the comparison
$h_x(T)\le2\widehat h(T)+\log392/3$, and $x(2R)=(57-28s)/8$ of height $\log41$.

## Silverman

J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., cited at lines 1132-1149:
IV.1 (the parameters $z$ and $w$), IV.5.5 (the formal logarithm and its coefficients),
IV.6.3-6.4 (the logarithm is an isomorphism on $v(z)>e/(p-1)$), VII.2.1-2.2 (the reduction
kernel and the formal group).

## Multiplication certificate generator

`construction/multiplication-certificate.js` (project-authored): the definitions of
`raw_z`, `raw_inverse_x`, `log25`, `pole`, `test_group` (twelve tests, precisions
$1,\dots,1,25,25,25,25$), `slope` (normalizations $R_0(t-1)^2$ and $R_0^{25}(t-1)^{26}$, six
groups, the trace $2\sum_g(\omega_g)_0$) and `height_certificate`.

## Fixed constant prescription

`construction/fixed-certificate-constants.js` (project-authored): the prescription of
$P_0$, $W$, the catalogue, $N_s$, $M$, $c_*$, $\ell$, $D$, $G_0$, $E_0$, $R$, $Q$, $B_{\rm cm}$,
$C_{\rm cm}$, $A_{\rm height}$ and $T$, never evaluated.

## Six-contact finite checks

`construction/verify-six-contact.js` (project-authored): among other finite identities, the
clearing inequalities $2E_p-C_p-2D_p>v_p(12)$ and $2E_p-C_p-2v_p(12)\ge4$ for
$B_p\in\{1,4\}$ and $v_p(12)\in\{0,1,2\}$.
