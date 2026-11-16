# Arithmetic inputs to the 198 Busy Beaver component

The asserted inputs in q198bb:inputs match the finished arithmetic component and the retained Version 18 results. No change of point, sign, scalar quotient, contact exponent, polynomial presentation, or quantifier was found. Three numerical statements need an explicit derivation when references are inserted: the canonical-height lower bound, the Lucas bound starting at \(c=8\), and the numerical real neighborhood. Those derivations are given below. They introduce no new arithmetic premise.

This is an author-side interface check. It checks the statements consumed by the Busy Beaver proof against their supplying text, including elementary numerical bridges. It is not independent acceptance of the arithmetic component, a fresh audit of every inherited foundation, or an audit of the quantitative geometry, record program, or state budget elsewhere in the Busy Beaver component. Neither component nor the manuscript was edited.

## Frozen sources

All paths below are relative to C:/Users/glaze/Documents/Codex/2026-11-02/lo/. All line numbers are one-based source lines.

| Key | File | SHA-256 |
| --- | --- | --- |
| BB | work/v18-198-bb-integration-20261115/height-bb/q198bb-proof.tex | b106b4addeab312d25b5097623ce6df3d79c01c0ba746bebd7d80399d27b8b24 |
| A | work/v18-198-bb-integration-20261115/arithmetic-component/arithmetic198.tex | 662b29ce83cf98429d7c251d8b530d296954c4231c912ee80a0370bb4a392f54 |
| V | work/version18-findings-20261114/cleanup-split/next-local-control/quartic_v18.tex | ca1ea465a0ebae934162a2c278186ab09477a91f14b60eefa71c5398ee71a165 |
| W | work/version18-findings-20261114/cleanup-split/combined-remaining-sources/quartic_v18.tex | 800e23b01fe33c2b612557fad7ca5d3802fae5654cbf397e1dbf8b42af8d9848 |

V is the public source after PR 111. W is the pending combined-source candidate. The inherited statements cited here are present in both. This report does not describe either candidate as already incorporated into a later receiving manuscript. The inherited contact-height proof consumes the product-averaging argument in q214:height-averaging, not the superseded quotient argument retained historically in q214:height-supplier.

## Complete map of the asserted inputs

| BB lines | Asserted input | Exact supplying text and check |
| --- | --- | --- |
| 55–61 | Absolute logarithmic height; \(K,\rho,d,D,E,R_0,P=2R_0\) | A 55–59 and 151–152, q198:inherited. BB's \(P\) is A's \(P_0\). Exact doubling gives \(x(2R_0)=57/8-7\rho/2\), \(y(2R_0)=-165/8+417\rho/32\), with the displayed sign. See also inherited subsec:v5-point-source. |
| 62–65 | Unique decomposition \(E(K)=\mathbb ZR_0+E[2](K)\); four torsion points | A 63–66, q198:inherited, consuming prop:generator after its stated normalization. V 5481–5483 and 5493–5497 identify this normalized curve and its full two-torsion. Since \(2E(K)=\mathbb Z(2R_0)\), every point differs from an integer multiple of \(R_0\) by two-torsion, uniquely. |
| 65 | \(\widehat h_E(P)\ge1/2\) | Inherited eq:o8-indexheight, V 14332–14341, W 14364–14373, on the exact normalized point \(P_*\). This is stronger than the positivity used in A. The explicit bridge is below. |
| 65–67 | Independence of the pointed conjugate images of \(R_0\) over \(\mathbb Z[i]\), modulo torsion | A 67–69, q198:inherited, and inherited v15:aggregate:lem:independent. Doubling a purported relation between the images of \(R_0\) gives the prohibited relation between the images of \(P_0\). The pointed isomorphisms are the same. |
| 68–70 | Real recurrence, finite preparation, CRT, simultaneous primes, prepared pole realization | A 125–149, q198:inherited, and the actual 198 applications q198:half-generator-reduction A 844–891, q198:half-generator-progression A 894–940, q198:scalar-preparation A 942–1015, q198:additive-contacts A 1017–1077, q198:completeness A 1079–1185. The inherited labels are listed below. The half-generator lemma is essential; the old assertion that a quarter group order annihilates a double cannot simply be applied to \(R_0\). |
| 72–76 | Four finite recovered points and \(n=m_1/2,\ a=m_2\ne0,\ t=m_3,\ b=2m_4+1\) | q198:reciprocal-pairs A 251–297; q198:inverse-vieta A 316–366; q198:recovery-order A 368–386; q198:scalar-ratios A 409–431; q198:affine-fourth A 434–458. A defines \(\nu([m]R_0+\tau)=m/2\) at 65–66 and the four labels at 445–446. Only \(Q_2\) must be non-torsion in soundness. Finite torsion differences in the other three blocks are permitted. In particular \(b\) is odd and nonzero even when \(m_4=0\). |
| 78–83 | \(T=7+\frac14\operatorname{Tr}\sum x(Q_i)\ge1\); \(t_0=\lambda,t_1=\lambda+T\); \(B,c\) | q198:shifted-aggregate A 560–587 and q198:scalar-extraction A 610–617. The inverse Vieta coordinate \(p\) is \(x(Q_2)\). All four points are finite, so \(x(Q_i)\ge-d\) at each real embedding, giving trace sum at least \(-24\). There is no multiplicative \(t_1=Tt_0\) in this family. |
| 85–90 | \(\beta=51x^2+2504,\ L_N,\ c\ge149^{L_N}\), scalar height bound, \(C_3=2^{330770}\) | q198:scalar-extraction A 610–658, especially 613–617. Its stronger statement is \(149^{L_N}M_5(\beta)^3\mid c\). The supplier of \(C_3\) is v15:height:thm:contactheight, quoted at A 95–98. Also \(L_N\ge N\) for every integer \(N\ge1\), since \((18N-9)/4\ge N\). |
| 92–97 | Contact height and two separate divisibilities | A 108–124, q198:inherited; q198:contact-circuit A 212–248; q198:half-index-comparison A 661–723; q198:residual-divisibility A 724–747. Each \(t_j\) avoids \(\Theta\), but \(t_j=1\) is allowed and has radical one. Each \(M_j^3\mid\Delta\) and each \(M_j\mid J_x\) is separate. No coprimality or divisibility by the product of the radicals is asserted. |
| 98–104 | Exact Lucas residual, integer domain, reduced-numerator bound | q198:residual-divisibility A 727–746. The minus sign on \((a+1)(a-1)tb\), the square \((a-1)^2b^2\), and the final \(-1\) match. The half-integral first label accounts for the factor 4 in \(J_x\le4Be^{h(\beta)}\). Extending the reduced numerator by zero when \(\beta=n\) is harmless; only nonzero residuals are used in divisibility-to-size arguments. |
| 105–113 | \(C_2<2^{7557/32}\), \(\alpha=2103/1024\), \(H_2=\log7+C_2B_\Sigma^\alpha\), exceptional set, coarse numerical bounds | A 108–124 supplies the radical domain and height inequality. Numerical suppliers are q214:height-supplier, V/W 3168–3182, and P10 of q214:uniform-existence, V/W 2279. The operative geometric route is q214:height-averaging. The set \(\Sigma=\{p:p\le76176\}\cup\{2029147\}\) is A 113. The elementary numerical enlargements are checked below. |
| 114–124 | Affine norm-one classification and Lucas lower bound for \(c\ge8\) | q198:affine-lucas A 749–795. A's statement says “sufficiently large,” but its proof A 764–788 gives BB's explicit \(c\ge8\) range, as checked below. BB's \(A',c',w\), including the sign of \(A'\), are A's \(A,c',w\). |
| 125–126 | \(J_x=0\) implies integer input | q198:integer-input A 798–806. The squarefree integer is 102, because \(n\) may be half-integral. The former squarefree-51 argument for integer indices is not used here. |
| 128–129 | Physical scalar quotient \(Z=2z(Q_2)/z(H)\), \(z=-x/y\) | q198:scalar-ratios A 409–431, specifically 412–418. The stored equation is \(Z_{\rm st}(M+W)=-2S\); the physical variable is \(Z=RZ_{\rm st}\). No factor \(R\), factor 2, or sign is missing. q198:recovery-order establishes the reference denominators first. |
| 130–138 | \(R,r_s,F,W_s,b_s\), including powers 10, 5, 4 and constant 9792 | q198:nonzero-scale A 299–313; q198:inherited A 80–98; q198:scalar-preparation A 955–977. \(F\) is the norm of the reciprocal abscissa. The powers and 9792 match. Positivity and \(F\ne0\) are established before quotient interpretation at A 368–386. |
| 139–145 | Ordered preparation; \(Q_2=[a_0]P,\ 3\mid a_0\); fixed contact list with incidences; final progression; fresh pole certificates | q198:scalar-preparation A 978–1014; q198:additive-contacts A 1019–1051; q198:half-generator-progression A 895–939; q198:completeness A 1085–1118 and 1167–1175. The order, component condition and explicit prime set are expanded below. |
| 146–149 | Only uniform completeness restriction is the scalar real bound; later data may depend on \((N,x)\) | A 968–970 and 1182–1184 prove this claim. Although A 1080–1081 allows a fixed enlargement of \(N_C\), its proof introduces no second independent restriction: choose \(a_0\) arbitrarily large for the Lucas converse for each \((N,x)\). BB's own q198bb:real, 501–588, supplies an explicit real bound and uses the same ordered preparation. |
| 151–157 | Unbalanced height, \(K_0,H_0\), degree, content and support for all \(N\ge1\) | A 7–23 and q198:finite-algebra A 1207–1270. The exact formula is \(P_A=\mathcal P_0-2AY_{103}-44402AY_{103}^2Y_{115}+A^2Y_{103}^2\). The largest fixed coefficient is \(H_0\), and \(A_N\ge149^3>44402\), giving \(\max(H_0,A_N^2)\). The input fourth-power coefficient is 1. BB's strict \(H_0<149^{214}\) is an exact integer strengthening of A's written weak comparison, checked below. |
| 158–160 | Balanced table not selected | A 7–8, 14–23 and q198:bb-interface A 1284–1294 fix the unbalanced presentation and polynomial dependence on \(A\). The balanced comparison has no role in the selected theorem or this arithmetic-input check. |

## Numerical bridges and scope checks

### Canonical height on the same model

The normalized \(P_*\) in subsec:v5-point-source is BB's \(P=2R_0\). The proof immediately before eq:o8-indexheight gives

\[
2\widehat h_E(P_*)\ge\log41-\tfrac13\log392>1.
\]

Alternatively, divide \(h(x(nP_*))\ge n^2-6\) by \(n^2\) and pass to the canonical-height limit to obtain \(2\widehat h_E(P_*)\ge1\). Both give the consumed bound. Transport by the stated pointed isomorphism preserves canonical height. The source does not assert \(\widehat h_E(R_0)\ge1/2\); the consequence for that point is \(\widehat h_E(R_0)\ge1/8\). Thus BB's later \(6\widehat h_E(R_0)\ge3/4\) has the correct normalization.

### The explicit Lucas range

Suppose \(\Delta=0\), \(c=|a|\ge8\), and \(b\ne0\). Then \(c'=|a+1|\ge c-1\ge7\), and \(w=\operatorname{sgn}(a+1)(a-1)b\ne0\). The norm-one argument in A 764–775 applies since \(c'>2\). It yields \(j\ge1\), \(|w|=U_j(c')\), and \(|t|\in\{U_{j-1}(c'),U_{j+1}(c')\}\).

If \(a+1>0\), reduction modulo \(c'-2=|a-1|\) shows that this modulus divides \(j\). If \(a+1<0\), reduction modulo \(c'+2=|a-1|\) gives the same conclusion with that modulus. Thus \(j\ge c'-2\ge5\). The recurrence bound and \(B\ge|t|\) give

\[
\log B\ge(j-2)\log(c'-1)
\ge(c'-5)\log(c'-2)
\ge(c-6)\log(c-3).
\]

Both factors in each weakened product are positive when \(c\ge8\). This proves BB 114–124 from q198:affine-lucas; no new Lucas theorem or numerical hypothesis is required. The converse used for completeness still only needs an arbitrarily large positive \(a=2a_0\in6\mathbb Z\), supplied for each input by q198:scalar-preparation.

### Contact constants

The \(C_2\) at BB 105 is the contact-supplier constant from V/W 3170–3182. It is not the separately scoped logarithmic additive constant called \(C_2\) in A 825–826. The notation does not identify the two constants.

Because \(2029147<2^{21}\) and \(76176<2^{17}\),

\[
B_\Sigma\le2029147\,76176^{76176}<2^{21+17\cdot76176}=2^{1295013}.
\]

Since \(\alpha<7/3\),

\[
C_2B_\Sigma^\alpha
<2^{7557/32+(7/3)\cdot1295013}
=2^{96701861/32}<2^{3999999}.
\]

Adding \(\log7\) still gives \(H_2<2^{4000000}\). These enlarge constants from the same exceptional set; they do not replace the height supplier. P10's reflected height conclusion applies here. Its later multiplicative aggregate identity is replaced by A's additive identity.

### The numerical real neighborhood and factor two

A 957–970 uses fixed bounded real neighborhoods with unspecified constants. BB 507–558 constructs a permitted numerical choice. It takes the identity component of the closure of the paired \(P\)-orbit, whose projections onto both real identity circles are surjective. The measure estimate supplies a compact neighborhood away from the finitely many reference exceptions with both \(|z(H)|>1/2000\). The scalar point can lie in a fixed neighborhood of the identity with both \(|z(Q_2)|\le1\). Neither choice depends on \(N\) or the input.

The actual doubled quotient therefore satisfies \(|Z|<4000\) at both embeddings. As

\[
Z_0=(Z+Z^\sigma)/2,\qquad Z_1=(Z-Z^\sigma)/(2\sqrt2),
\]

both rational components are below \(2^{12}\) in absolute value. At either embedding \(H\) lies on the real identity component, so \(x(H)\ge d_\pm>0\); since \(d_+d_-=7\), one has \(|F|\le1/7\). For \(R\ge1\),

\[
0<W_s<(2^{48}+2^{24}+1)R^{-4}<2^{49}R^{-4},\qquad
0<b_s<9793\,2^{98}R^{-6}<2^{112}R^{-6}.
\]

Here \(R+9792\le9793R\), so the range really is \(R\ge1\). No additional assumption \(R\ge9792\) is needed. In particular \(R\ge2^{20}\) gives \(b_s<2^{-8}<17\). This matches A 91–92 and its estimate with abstract constants at 962–966.

The paired \(P\)-orbit used to choose this neighborhood and the paired \(R_0\)-orbit used for the final numerator maps are compatible. Since \(P=2R_0\), multiplication by two is onto their common identity torus. The final progression must retain the component-order divisibility for the \(R_0\)-orbit, as A 930–938 requires. Its point functions are \(H=[2h]R_0\), \(U_i=[hm_i]R_0\), and \(V_i=[hm_i-m_i]R_0\), all integer multiplication maps. A scalar congruence alone does not impose a real-neighborhood condition.

### Completeness order and quantifiers

The full content of BB's compressed preparation paragraph is the following order in A:

1. Fix the scalar real neighborhood and its uniform lower bound on \(N\). For integer input, \(r_s\ge1\), so \(R\ge149^{2N+1}/(1+149^2)\), uniformly in the input.
2. For the particular \((N,x)\), prepare the odd-valuation numerator support of \(R(R+9792)\), and explicitly include \(2,3,17\), even when absent from that support. This is A 978–980.
3. Choose \(H_*=[h_*]P_0\), with \(64\mid h_*\) already imposed, at the required finite depths and in the selected real neighborhood. Then choose an arbitrarily large, sufficiently divisible \(a_0>0\), with \(3\mid a_0\), and \(Q_2=[a_0]P_0\) in its fixed real neighborhood. This is A 982–995. Doubling the quotient preserves odd-prime depths and increases its dyadic valuation; it does not change the final pole depth requirements \(3,1,2\).
4. Hold \(a_0\) fixed. Continuity preserves scalar conditions on a finite and real neighborhood of \(H_*\). Choose \(L\) with \(64\mid L\), the finite divisibilities and required real component orders. Retain the real neighborhood separately. This is A 1005–1014.
5. Choose the Lucas labels, fix all four points and \(T\), and then fix and merge \(\Theta\cup(\Theta-T)\), retaining every incidence. Fix prime, slope, finite-avoidance and denominator requirements before the simultaneous-prime theorem. This is A 1085–1114 and 1019–1051.
6. Use the half-generator reduction lemma and compatible final progression, preserving the neighborhoods. After the final \(H\) is fixed, realize fresh pole certificates for \(b_s(H)\), \(b_0\), and \(b_1\), separately. This is A 1114–1175. An earlier scalar certificate is not reused.

The first step sets the only uniform completeness threshold. Later indices, moduli, cutoffs and witnesses may depend on \((N,x)\). Make \(a\) large for the Lucas converse by increasing \(a_0\), not by introducing a new uniform threshold on \(N\). These are the quantifiers used by BB 139–149 and 575–588.

### Soundness threshold and separate radicals

The arithmetic proof has an existential \(N_S\) in q198:soundness, A 808–837. The BB component supplies a numerical upper bound for a sufficient threshold using its own record argument. It does not assume A already proved its particular \(G(r_*)\).

Once BB proves \(B^2\le M_1h(T)+M_2\), A 590–607 applies with those constants. Since each \(M_j^k\mid J\) separately, each \(M_j^k\le|J|\), and thus

\[
B^2\le2M_1H_2|J|^{7/(6k)}+(M_2+M_1\log2).
\]

With BB's \(M_1=18U,\ M_2=10U(r_*+1)\), its \(C=36UH_2\) and \(J_1=32U(r_*+1)\) majorize these terms. Use \(k=3,\ J=\Delta\) and \(k=1,\ J=J_x\) in the two contradictions. Contact coincidences between detectors cause no problem because no product of their radicals is taken. The factors 14 and 4 and exponent \(7/6\) are those in A.

The all-larger-parameter statement in q198:family is \(N\ge\max(1,N_S,N_C)\), A 1273–1281. BB's q198bb:threshold-arithmetic and q198bb:real supply sufficient bounds for those two tasks, and q198bb:threshold connects the bound to the Busy Beaver parameter. The coefficient crossover \(N=53\) is separate and is never used as a defining threshold.

### Finite coefficient comparison

Exact integer arithmetic confirms

\[
149^{210}<(5898050446009651968\cdot31581660^{28})^2<149^{214}.
\]

The strict comparison in BB 155 follows from the actual \(H_0\), even though A 1269 writes a weak upper relation. No coefficient has changed. BB's \(Q_i(A)\) are A's residuals before specializing \(A=A_N\). There are 184 residuals and 198 total coordinates, so the existential tuple has 197 coordinates. The conversion \(x_1=X,\ x_i=Y_{i-1}\) explains \(Y_{103}\) and \(Y_{115}\) in the parameter terms.

## Inherited labels for assembly

These label locations were checked in both frozen manuscript sources. Their supplying proofs should remain internal references in the assembled manuscript.

| Label | V line | W line |
| --- | ---: | ---: |
| prop:generator | 5468 | 5469 |
| subsec:v5-point-source | 17020 | 17052 |
| eq:o8-indexheight | 14339 | 14371 |
| v15:aggregate:lem:independent | 37164 | 37209 |
| q214:uniform-existence | 2232 | 2232 |
| q214:height-supplier | 3046 | 3046 |
| q214:height-averaging | 3188 | 3188 |
| v222:contacts | 42682 | 42727 |
| v15:height:thm:contactheight | 36308 | 36353 |
| v15:logs:thm:uniform-logarithm-tail | 37344 | 37389 |
| v15:logs:cor:uniform-logarithm-ratio | 37378 | 37423 |
| q214:factor-source | 4115 | 4115 |
| thm:v5-simultaneous-primes | 22780 | 22824 |
| lem:v5-two-reductions | 17432 | 17464 |
| v15:dependencies:lem:arbitrary-avoidance | 37735 | 37780 |
| v15:dependencies:lem:rational-contacts | 37815 | 37860 |
| v15:dependencies:cor:compatible-progressions | 37777 | 37822 |
| v15:dependencies:lem:real-progression | 37834 | 37879 |
| v5:preparation-zero-bridge | 16851 | 16883 |
| v15:dependencies:sec:poles | 37864 | 37909 |
| v15:dependencies:lem:conic-complete | 37910 | 37955 |

For the receiving headline, q198:family, q198:finite-algebra, q198bb:threshold and q198bb:coefficient are the direct result chain. The detailed arithmetic references justify replacing the standalone phrase “Subject to the arithmetic premises” with internal references in the assembled unconditional theorem. That editorial integration is root's responsibility. This report does not certify the remaining BB proof or pending foundation changes beyond the arithmetic-input comparison described here.
