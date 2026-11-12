# Locators for the Route K chapter

Route K is not in the manuscript. It changes the pole polynomial of Section 5 to the
congruent number curves $y^2=x(x-\ell)(x+\ell)$ and replaces the restricted converse
(Theorem 5.3) and the simultaneous descent of Section 5.1 by an explicit descent lemma and one
narrow hypothesis on congruent number curves. The mathematics is written in project-authored
research notes in `docs/research/` of this repository; they are specifications written for
this project, not published sources. The deep theorems that the hypothesis CR₃ rests on are
cited at the end.

## Soundness for the congruent number curves

`docs/research/rv-route-k.md` §4.1: Lemma 5.1 re-derived for the pole polynomial with the
curves $x+\ell$. The step $v_p(x+3\ell)=\min(v_p(x),v_p(\ell))$, which needs $p\ne3$, becomes
$v_p(x+\ell)=\min(v_p(x),v_p(\ell))$ for every prime $p$.

## Points and the pole polynomial

`docs/research/rv-route-k.md` §4.2: a point of $C_\ell$ with abscissa $\beta$ up to squares,
the reformulation of $\Phi$ through two points with abscissas in $\beta\mathbb Q^{*2}$, and the
torsion bookkeeping. The rescalings that turn points of $C_N$ and $C_{N\theta}$ into pole
witnesses are those of the Lean proof (module docstring of `RouteK/Assembly/Points.lean`).

## Inputs and the properties of theta

`docs/research/slot-k.md` §1.1, recalled from `docs/research/descent-alt.md` §3.1 and the
manuscript's Section 5.1 (lines 1027–1033): admissible inputs, $\beta=\mathrm{sqf}(mB)$,
$\theta=\mathrm{sqf}(m(m-B))$ and the properties (θ1)–(θ4) with their proof.

## Certificates and the descent lemma

`docs/research/slot-k.md` §1.2 (certificates of torsion and of Selmer type) and §1.3 (the
statement of DL and the two call sites of pole completeness).

## Configurations and the Selmer system

`docs/research/slot-k.md` §2.1: configurations, reciprocity, the product class, Monsky's matrix
and the system $\Sigma(\mathcal C)$ with its rows E1, E2, (R) and (D).

## Proposition 0

`docs/research/descent-alt.md` §4.1: for an odd squarefree $d>0$ the system $\Sigma(\mathcal C_d)$
is the 2-Selmer group of $C_d$ in coordinates; the place-2 table was checked against an
independent exact descent on 600 curves. `docs/research/slot-k.md` §2.1 rechecks by hand the
structure of the place-2 rows and the rows for $c=5$.

## Partner and gluing lemmas

`docs/research/slot-k.md` §2.2: Lemma 1 (partner) and Lemma 2 (gluing), with the inverse
formulas (2.1) and (2.2).

## Base configuration

`docs/research/slot-k.md` §2.3: Lemma 3, the configuration $\{p^*,q_0\}$ with classes $7$ and $3$.

## Slots

`docs/research/slot-k.md` §2.4: step 0 (the multiplier), the slot primes $q_0$, $r_p$, $r_\ell$,
their existence by the Chinese remainder theorem and Dirichlet's theorem, and the reverse
symbols by reciprocity.

## Proof of the descent lemma

`docs/research/slot-k.md` §2.5, steps 1–6: the first curve through Lemmas 1, 2 and 3, the
second curve through Lemma 2 with the primes of $\theta$ glued onto $q_0$.

## The Lean plan

`docs/research/slot-k.md` §4.1 (the narrowed hypothesis CR₃ and its justification) and §4.2
(the lemmas L1–L6 and the chain $\mathrm{L1},\mathrm{L2},\mathrm{L3}\Rightarrow$ configurations;
$\mathrm{L4},\mathrm{L5}\Rightarrow$ certificates; $\mathrm{CR}_3\Rightarrow$ points;
$\mathrm{L6}\Rightarrow\Phi$).

## The deep input on published theorems

`docs/research/tyz-5b.md` §1 (Tian–Yuan–Zhang, the form of their Theorem 3.5(2) that is used,
and what Gross–Zagier–Kolyvagin add), §§2–4 (row 5b of Smith's determinants, proved by forest
expansion, and its value $1$ on a curve with 2-Selmer dimension $3$ and a first coordinate
$\equiv3\pmod4$), and §5 (the curves of the slot construction). `docs/research/rv-route-k.md`
§4.3 checks the hypotheses of Kriz's theorem for the curves $C_d$.

## The trust statement for CR3

`docs/research/cr3-trust.md`, a project-authored note: the forms of the hypothesis CR₃ that the
variants of the main theorem take, and the implications between them (§0); a numbered outline of
the argument for the class-number form in positive-rank form, with a supplier and a status for
every step (§1): the match of the statement with Tian–Yuan–Zhang's quantities (Part A), their
deep results (Part B), Proposition N (Part C), Gross–Zagier with an auxiliary imaginary quadratic
field from Bump–Friedberg–Hoffstein, Waldspurger or Friedberg–Hoffstein, with the theorem numbers and
the level still to be checked (Part D, which also records that the manuscript's Lemma 5.5
and Kriz's 2-converse are not used), and the steps proved here (Part E); and what remains outside
refereed sources (§2). `docs/research/rv-cr3-trust.md` is a model review of that note.

## Kriz

D. Kriz, *Supersingular main conjectures, Sylvester's conjecture and Goldfeld's conjecture*,
arXiv:2002.04767v5 (2022), Theorems 10.13 and 10.17(2): the 2-converse theorem in rank one
for curves with CM by $\mathbb Z[i]$. An unrefereed preprint. With the corank lemma it is an
alternative route to rank one that the hypotheses do not need (`docs/research/nt-tyz.md` §5.1).

## Tian-Yuan-Zhang

Y. Tian, X. Yuan and S.-W. Zhang, *Genus periods, genus points and congruent number problem*,
Asian J. Math. 21 (2017), no. 4, 721–774 (read in arXiv:1411.4728v1), Theorem 3.5 (first
assertion) and the argument of the proof of Theorem 3.5(2) in §3.3, as completed in
`docs/research/nt-tyz.md` §4 by Proposition N (no readable version of Tian–Yuan–Zhang states this
form directly, nt-tyz Verdict 1): for squarefree $n\equiv5\pmod8$, an odd genus sum $T_{5b}(n)$ makes
$L(C_n,s)$ vanish to order exactly one at $s=1$.

## Gross-Zagier-Kolyvagin

The manuscript's Lemma 5.5 (`lem:forward-rank`, line 1086): analytic rank one implies rank
one, by Gross–Zagier and Kolyvagin. The trust statement for CR₃ does not use it: Gross–Zagier over
an auxiliary imaginary quadratic field gives rank at least one, which is all that is needed
(`docs/research/cr3-trust.md` §1, D4).

## Cassels-Tate

The manuscript's corank lemma (`lem:corank`, line 1072): for an elliptic curve with full
rational two-torsion, a 2-Selmer group of dimension $3$ gives $2^\infty$-Selmer corank one. The
proof uses only that the Cassels–Tate pairing on $Ш/Ш_{\rm div}$ is nondegenerate and alternating,
so $\dim(Ш/Ш_{\rm div})[2]$ is even; no finiteness of $Ш$ is assumed. For elliptic curves this is
due to J. W. S. Cassels, J. reine angew. Math. 211 (1962), as `docs/research/pc-audit.md` RK3 cites
it; the title (*Arithmetic on curves of genus 1. IV. Proof of the Hauptvermutung*) and the pages
95–112 were not checked against the journal. The manuscript cites B. Poonen and
M. Stoll, *The Cassels–Tate pairing on polarized abelian varieties*, Ann. of Math. 150 (1999).
`docs/research/pc-audit.md` RK3 and `docs/research/rv-cr3-dl.md` §2.2 check the argument.
