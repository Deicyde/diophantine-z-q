# Locators for the row-5b chapter

The row-5b determinant is not in the manuscript. Its mathematics is written in the
project-authored research note `docs/research/tyz-5b.md` of this repository, a specification
written for this project and checked by an automated referee, not a published source. The
published works it uses, and the published theorems that the hypotheses CR₃^5b and CR₃^TYZ rest
on, are cited at the end.

## Notation

`docs/research/tyz-5b.md`, Notation: the bits $a_{ij}=(p_j/p_i)_+$, $y_i=(-1/p_i)_+$,
$z_i=(2/p_i)_+$, Smith's matrix $L$ (Smith's $A$), the matrices $M_1$ and $M_{5b}$, and the genus sum
$T_{5b}(n)$ of row 5b of Smith's Table 2.

## Lemma 2.1

`docs/research/tyz-5b.md` §2.1: the forest lemma, $\det L[U\setminus F,U\setminus W]$ as a sum over
the forests rooted at $F$ with one element of $W$ in every tree, and its proof (expansion of the
diagonal, cancellation of cycles, the unique compatible bijection of a forest). The section states
that all determinants are taken over $\mathbb F_2$, where they equal permanents.

## Lemma 2.2

`docs/research/tyz-5b.md` §2.1, Consequences and Lemma 2.2: $\kappa_\rho(B)$ counts spanning
arborescences; the column sums $c_v=y_v(1+y(B))$; equal cofactors when $y(B)=1$;
$\det L_B[B\setminus j,B\setminus i]=\kappa_j(B)$; and the $\kappa$-difference
$\kappa_i+\kappa_j=\sum_\varphi\mathrm{wt}(\varphi)c(T_i(\varphi))$.

## Proposition 2.3

`docs/research/tyz-5b.md` §2.2: Rédei's formulas $g(B)=\kappa(B)$ if $y(B)=1$ and
$g(B)=\sum_\rho z_\rho\kappa_\rho(B)$ if $y(B)=0$ (rows $n\bmod4=3,1$ of Smith's Table 1), and the
consequences (2.1) and (2.2). The row-5b chapter takes the right-hand sides as the definition of
Rédei's $g$. Their derivation from genus theory is followed, by a different route, in the Rédei
chapter.

## Propositions 3.3 and 3.4

`docs/research/tyz-5b.md` §3.1: the forest forms of $\det M_1$ and $\det M_{5b}$ and their partition
forms. The formal proofs replace Lemmas 3.1 and 3.2 and the involution expansion by a rank-one update
and the matrix $P(c,d)=\begin{pmatrix}D_d&L^{\mathsf T}\\L&D_c\end{pmatrix}$.

## Proposition 3.5

`docs/research/tyz-5b.md` §3.2: for $y(S)=0$, the sums of $\prod g(B)$ over the partitions into
class-1 blocks and into class-3 blocks agree (row 1 of Smith's Table 2), by comparing forest sums and
counting perfect matchings of trees.

## Theorem 3.6

`docs/research/tyz-5b.md` §3.3: Theorem 3.6, $T_{5b}(n)=\det M_{5b}$ for $n\equiv5\pmod8$ (Smith,
arXiv:1603.08479, Theorem 2.2, row 5b of Table 2). The note checks it on random abstract data and on
PARI class groups (§6), and `docs/research/rv-cr5b-sec3.md` §4 checks $T_{5b}=\det M_{5b}$ against
PARI on 30 values of $n$.

## Lemma 4.1

`docs/research/tyz-5b.md` §4.1: for odd squarefree $n\equiv5\pmod8$ the Selmer system of
`docs/research/slot-k.md` §2.1 for the class $c=5$, the torsion classes $(-1,-n)$ and $(n,2)$, the
subspace $H$ ($b_1=0$, $a_0=\lambda\cdot u$) and the isomorphism $H\cong\ker M_1$,
$(a,b)\mapsto(u+v,u)$. The Lean proof works first for any configuration of product class $5$
and then transfers to $\mathrm{Sel}_2(C_n)$ through Proposition 0.

## Lemma 4.2

`docs/research/tyz-5b.md` §4.2 (recalled from `docs/research/pc-audit.md`, rule RK6): the
determinant of a symmetric corank-one matrix over $\mathbb F_2$ bordered by a vector. The note
proves it with the adjugate; the Lean proof argues with kernels instead (module docstring of
`RouteK/Rank5b/Bordered.lean`).

## Theorem 4.3

`docs/research/tyz-5b.md` §4.2: the rule of row 5b, $\det M_{5b}=\sum_{p\mid a}y_p$ for a
non-torsion Selmer class on a Selmer-minimal curve.

## Corollary 4.4

`docs/research/tyz-5b.md` §4.2: a first coordinate $\beta$ with $|\beta|_{\rm odd}\equiv3\pmod4$
forces $\det M_{5b}=1$. The Lean statement takes the 2-adic shape of CR₃^Sel,
$|a|\equiv7\pmod8$.

## Row 5b of Smith's table

`docs/research/tyz-5b.md` §§2–3: the forest lemma, Rédei's formulas in terms of the cofactors
$\kappa_\rho(B)$, and Theorem 3.6, $T_{5b}(n)=\det M_{5b}$ for $n\equiv5\pmod8$ (Smith's Theorem 2.2,
row 5b, reproved). Theorem 3.6 of the row-5b chapter follows these sections with one change of route:
both sides are written as the same forest sum, the determinant through a rank-one update of the
matrix $P(z,y)$ and the genus sum through a marked form glued along the partition. So the proof does
not pass through Proposition 3.5 or the partition form of Proposition 3.4, which are proved
separately. Rédei's formulas are proved from genus theory in the Rédei chapter.

## The hypothesis in Tian-Yuan-Zhang form

`KERNEL_PLAN.md`, the paragraph beginning "That step is done": the hypothesis CR₃^TYZ (for
squarefree $n\equiv5\pmod8$ with $\#\mathrm{Sel}_2(C_n)=8$ and $T_{5b}(n)$ odd, every Selmer class
comes from a rational point) and its trust statement, which names Tian–Yuan–Zhang through
Proposition N, Rédei's formula and Gross–Zagier. `docs/research/rv-cr5b-sec3.md`: a referee report
on CR₃^TYZ, covering its definitions ($\kappa$, $g$, $T_{5b}$ and the edge cases, §1), its trust
statement (§2) and the proof chain to CR₃^5b (§3), with a numeric red team against PARI on 30 values
of $n$ (§4). The class-number form CR₃^TYZ_Cl is located in the locators of the Rédei chapter.

## Proposition N

`docs/research/nt-tyz.md` §4: Proposition N. For squarefree $n\equiv5\pmod8$, if
$T_{5b}(n)=\sum_{d_0\equiv7,\,d_1\equiv3}g(d_0)g(d_1)\mathcal L_1(n/d_0d_1)$ is odd, then
$\mathcal L(n)\ne0$ and $\operatorname{ord}_{s=1}L(C_n,s)=1$ (the note writes $E_n$ for $C_n$). It is proved
from Tian–Yuan–Zhang's Theorem 3.5 (first assertion), Theorem 3.3 (the $\varepsilon$-classes of the
recursion), Proposition 3.2(1), Lemmas 3.16, 3.18 and 3.21, Lemma 2.8, Proposition 2.3 and the
recursion of their §3.1. §4.5 gives the recommended citation; their Theorem 1.2 must not be cited in
its literal form. Proposition N is not refereed; it has two model reviews,
`docs/research/rv-nt-tyz.md` and `docs/research/rv-prop-n.md` (the second written without the source
text of Tian–Yuan–Zhang; verdict: it holds as stated, relative to the inputs as quoted, with
presentational corrections recorded at the end of `docs/research/nt-tyz.md`).

## Validation

`docs/research/tyz-5b.md` §6: random checks of the lemmas on abstract data and on actual curves,
and the slot curves; §7 records an independent automated referee run.

## Tian-Yuan-Zhang

Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent number problem*,
Asian J. Math. 21 (2017), no. 4, 721–774; arXiv:1411.4728. Theorem 3.5(2) and its proof in §3.3;
`docs/research/tyz-5b.md` §1.2 locates the form used (if $T_{5b}(n)$ is odd, then
$2^{-\rho(n)}\mathcal L(n)$ is odd) in that proof; the form used holds as completed by
Proposition N (see above), not by Proposition 3.4 as written (`docs/research/nt-tyz.md` §2.3).

## Gross-Zagier-Kolyvagin

The manuscript's Lemma 5.5 (`lem:forward-rank`): analytic rank one implies rank one, by Gross–Zagier
and Kolyvagin. The justification of the hypotheses here does not use it: Gross–Zagier over an
auxiliary field (below) gives rank at least one, which is all that is needed
(`docs/research/cr3-trust.md` §1, D4).

## Gross-Zagier over an auxiliary field

B. Gross and D. Zagier, *Heegner points and derivatives of L-series*, Invent. Math. 84 (1986),
225–320, applied with an auxiliary imaginary quadratic field $K$ that satisfies the Heegner
hypothesis and has $L(C_n^K,1)\ne0$ (Bump–Friedberg–Hoffstein). `docs/research/cr3-trust.md` §1,
D2 names the suppliers: Bump–Friedberg–Hoffstein, Waldspurger, or Friedberg–Hoffstein, not
Murty–Murty (the derivative case); their theorem numbers, and whether the level $32n^2$ is allowed,
are still to be checked. The curve $C_n$ is modular because it has complex multiplication by
$\mathbb Z[i]$. Only "analytic rank one implies rank at least one" is used;
Kolyvagin's theorem is not needed (`docs/research/pc-audit.md` RK7).

## Smith

A. Smith, *The congruent numbers have positive natural density*, arXiv:1603.08479, Table 2 and
Theorem 2.2. Only the matrix of row 5b is used; its identity with the genus sum is reproved in the
note.

## Matrix-tree theorem

S. Chaiken, *A combinatorial proof of the all minors matrix tree theorem*, SIAM J. Algebraic
Discrete Methods 3 (1982), no. 3, 319–329, cited by `docs/research/tyz-5b.md` §2.1 (which gives only
the journal and year). Lemma 2.1 is its case over $\mathbb F_2$; the title, issue and pages were not
checked against the journal here.
