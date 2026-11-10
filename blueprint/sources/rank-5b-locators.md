# Locators for the row-5b chapter

The row-5b determinant is not in the manuscript. Its mathematics is written in the
project-authored research note `docs/research/tyz-5b.md` of this repository, a specification
written for this project and checked by an automated referee, not a published source. The
published theorems that the hypothesis CR₃^5b rests on are cited at the end.

## Notation

`docs/research/tyz-5b.md`, Notation: the bits $a_{ij}=(p_j/p_i)_+$, $y_i=(-1/p_i)_+$,
$z_i=(2/p_i)_+$, Smith's matrix $L$ (his $A$), the matrices $M_1$ and $M_{5b}$, and the genus sum
$T_{5b}(n)$ of row 5b of Smith's Table 2.

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

`docs/research/tyz-5b.md` §§2–3: the forest lemma, Rédei's formulas and Theorem 3.6,
$T_{5b}(n)=\det M_{5b}$ for $n\equiv5\pmod8$ (Smith's Theorem 2.2, row 5b, reproved). Not
formalized; it is part of what CR₃^5b rests on.

## Validation

`docs/research/tyz-5b.md` §6: random checks of the lemmas on abstract data and on actual curves,
and the slot curves; §7 records an independent automated referee run.

## Tian-Yuan-Zhang

Y. Tian, X. Yuan, S.-W. Zhang, *Genus periods, genus points and congruent number problem*,
Asian J. Math. 21 (2017), no. 4, 721–774; arXiv:1411.4728. Theorem 3.5(2) and its proof in §3.3;
`docs/research/tyz-5b.md` §1.2 locates the form used (if $T_{5b}(n)$ is odd, then
$2^{-\rho(n)}\mathcal L(n)$ is odd) in that proof.

## Gross-Zagier-Kolyvagin

The manuscript's Lemma 5.5 (`lem:forward-rank`): analytic rank one implies rank one, by
Gross–Zagier and Kolyvagin.

## Smith

A. Smith, *The congruent numbers have positive natural density*, arXiv:1603.08479, Table 2 and
Theorem 2.2. Only the matrix of row 5b is used; its identity with the genus sum is reproved in the
note.
