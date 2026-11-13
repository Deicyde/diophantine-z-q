# Locators for the $j$-form of the height hypothesis

Line numbers refer to `diophantine_zq.tex` in this repository (the 11/5 manuscript, SHA-256
`cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`, as in
[the manuscript entry](manuscript.md)); the notes in `docs/research/` and `KERNEL_PLAN.md` are
project-authored, not published sources; `docs/research/rv-lit.md` is a model review of the $j$-form and its
return to $u$, not a referee report.

## The Hauptmodul value

Section 4 (`sec:height`), lines 377-383, the definitions before `thm:height` (line 404): the contact set $\mathcal C=\{0,-15,-20,-24,-30,-60\}$,
$F(u)=u(u+15)(u+20)(u+24)(u+30)(u+60)$ and $G(u)=7u^2+300u+3600$. Line 510, in the proof: "Pull back
by $J(u)=-57600F(u)^2/G(u)^6$". Lines 949-950: with $j=a/b$ in lowest terms, the polynomial
$-57600bF(X)^2-aG(X)^6$ has $u$ as a root, so the $j$ of the last steps is $J(u)$.
`docs/research/rv-lit.md` §4, paragraph "$J$ is the value F2 bounds": the polynomials and the map
match these lines, and $J(u)$ is finite because $G$ has no rational root. `docs/research/h-b1.md` M7
records the same map.

## The j-form of H

The manuscript's steps whose combination gives the $j$-form: lines 900-905 (step E4,
$\max(1,h_F(A))\le\max(1,C_{\rm cm},Q_R^{17})M_S(u)^{24}$), lines 908-926 (step F1,
$j=3779136(\prod z_m)^4/(\sum z_m^8)^5$ in the even theta constants; the manuscript cites Lin–Yang
eq. (2) at line 911, which the trust statement replaces, see The trust statement for H), lines
927-932 (step F2, $h(j)\le40h([z_m])+22$) and lines 934-947 (step F3, $h([z_m])\le10^4\cdot2^{24}X$ with
$X=\max(1,h_F(A))$). The manuscript does not display the combined bound on $h(J(u))$;
`docs/research/rv-lit.md` (a model review of the $j$-form, not a published source) §4, paragraph "The constant", combines E4, F2 and F3 with $X\ge1$ into
$h(J(u))\le(40\cdot10^4\cdot2^{24}+22)\max(1,C_{\rm cm},Q_R^{17})M_S(u)^{24}$, and its paragraph
"Strength" records that this bound implies the minimal height hypothesis, so it is the stronger
hypothesis with the shorter justification.

`docs/research/wk-h.md`, Summary item 4 and §4.1 (the $j$-form as the residual hypothesis and the
proved return to $u$), and §6 (verdict: adopting it is the cheap win; it removes step F4 and the
final numerics from what is assumed, and the hypothesis is still a project statement).
`KERNEL_PLAN.md`, section "What can and cannot be formalized", the last two sentences of the
paragraph that contains the sentence beginning "`ZInQKernel/MainLiterature.lean` splits CR₃
further": the $j$-form is a
bound on the height of the Hauptmodul value $J(u)$, it implies the minimal height hypothesis (step
F4 and the final numerics), and its trust statement is steps A1-F3 of h-trust.

## Step F4

Lines 949-954: the manuscript's last step, the rational-root theorem applied to
$-57600bF(X)^2-aG(X)^6$, giving $h(u)<h(j)+74$. Lines 956-964: the final numerics,
$40\cdot10000\cdot2^{24}+96<10^{13}$, and the conclusion $h(u)\le\tfrac12H_6(S;R)M_S(u)^{24}$.
`docs/research/h-trust.md` §1, Part F, step F4 (content and status). `docs/research/wk-h.md` §4.1:
the two polynomial identities expressing $3a^7$ and $2^{10}3^85^6b^7$ through $F_h$ and $G_h$
(resultant $2^{18}3^{13}5^{10}$), the bound $C_0$ on the cancellation, the lower bound
$\max(|a|,|b|)^{12}\le10^{48}\max(57600F_h^2,G_h^6)$, and $12h(u)\le h(J(u))+450$, which replaces
the manuscript's inequality. `docs/research/rv-lit.md` §4, the paragraph on
$12h(u)\le h(J(u))+450$: it is a different inequality from the manuscript's, checked on 30 values of
$u$ (the six contact values and 24 others), with largest value of $12h(u)-h(J(u))$ equal to $49.1$,
and every cancellation divides $C_0$.

## The trust statement for H

`docs/research/h-trust.md`, as amended on 11-11 by task h-v16-adopt. h-trust Summary item 1: of
its 36 steps, 7 rest only on refereed theorems and scripts, 5 apply refereed theorems through
bookkeeping with only a model review, and 24 are manuscript or project arguments reviewed by models
only (F4, which the $j$-form does not assume, is one of them). Summary item 4 and §2 list what stays
outside refereed sources: the manuscript's own descent, conductor and transfer arguments, the
project replacements NoCM and Lemma PR, and the identification in step A4. Its §1 steps A1-F3 are the
justification of the $j$-form (`docs/research/rv-lit.md` §4: the $j$-form variants assume steps
A1-F3 and nothing else); step F4 and the final numerics are replaced by the proofs of the
$j$-form section. As amended: step F1 cites Lin–Yang Example 30 and eqs. (13)-(14), with the theta
expressions of Lauter–Naehrig–Yang and Igusa, and no longer Lin–Yang eq. (2) (Part F, F1); step
C8's finiteness of the twist is the determinant argument of the upstream manuscript's Version 14
(Weil pairing, Kronecker–Weber; cited in h-trust by Version 16 line numbers, V16 L660-667),
replacing local algebraicity of Hodge–Tate characters (Part C, C8); Versions 13-16 are later
unpublished revisions, not the 11/5 text above, and the argument is checked in
`docs/research/rv-up.md` §2.3, a model review. Kato, Astérisque 295 (2004), is a third option for
the $p$-adic Hodge theory of eigenforms, proposed for all levels from upstream's Version 14 on
(V16 L618-650); whether its §9.4 covers levels divisible by 5 is still to be checked (§2.5 item 3).
Four (not five) unrefereed editions cited by the manuscript are replaced
(§2.4). The same task amended steps A2, A4, C3, C8, E4 and F1 (h-trust preamble and changelog):
among them, Deligne 1971 locators for A4, the Galois choice of field in C3, and a second locator
for E4 (Gaudron–Rémond, Comment. Math. Helv. 89 (2014), §2.3 and Cor. 8.4, read only by upstream's model reviewer,
by no one here). Upstream context:
`docs/research/up-h.md` §2-§4, verified in `docs/research/rv-up.md` §2-§3.
`docs/research/wk-h.md` §5-§6 explains why the steps before F4 cannot be stated here.
