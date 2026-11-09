# Locators for the natural compiler chapter

Line ranges refer to `diophantine_zq.tex` in this repository (the 11/5 manuscript, SHA-256
`cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`). TeX labels are given
where the item has one. Section 10 has the label `sec:compiler`; its subsections have none.
The construction notes and generators in `construction/` are project-authored
specifications; they are listed after the manuscript items and serve as cross-checks, not as
inputs to the proof. The sources S21, S22, S23 and the universal interpreter source named in
Appendix B are not part of this repository.

## Section 1 input C

Section 1 (`sec:main`), lines 102-104: input $\mathsf C$ of Lemma 1.2 (`lem:assembly`): the
actual five-input natural polynomial and its rational translation have the exact
computation and substitution semantics of Section 10, including the power template. Lines
130-132 assign $\mathsf C$ to Section 10.

## Section 4 height constants

Section 4 (`sec:height`), lines 377-399: $\mathcal C=\{0,-15,-20,-24,-30,-60\}$,
$F(u)=u(u+15)(u+20)(u+24)(u+30)(u+60)$, the constants $F_0,D,G_0,E_0,Q_R,B_{\rm cm},C_{\rm cm}$,
$H_6(S;R)$ for $R\ge\max(D,\max S,10^{12})$, and the convention
$H_6(S)=H_6(S;\max(D,\max S,10^{12}))$.

## Section 4 height prime set

Section 4, lines 968-971: $S_{\rm ht}=\{p:p\le324\}$ is the prime set of the final value
argument.

## Section 10 signed encoding

Section 10 (`sec:compiler`), lines 5745-5750: $\operatorname{enc}(n)=2n$ for $n\ge0$ and
$-2n-1$ for $n<0$; the five natural inputs decode in the order $(n,\kappa,a,l,j)$.

## Section 10 decision predicate

Section 10, lines 5751-5764: rejection unless $n\notin\mathcal C$, $\kappa\ne0$, $a,l\ge1$,
$j=na$; $z=-x/y$ on nonzero multiples of $P_0$; $z([l]P_0)=u_l+v_ls$,
$\epsilon_l=|u_l|+|v_l|$, $r(a,j)=\frac12\operatorname{Tr}(z([j]P_0)/z([a]P_0))$;
$A^{(0)}_{\rm ht}=H_6(S_{\rm ht})$; the strict final tests $|r(a,j)-n|<\epsilon_l$ and
$4\epsilon_l<4^{-A^{(0)}_{\rm ht}|\kappa F(n)|^{24}}$.

## Section 10 reference program and IR

Section 10, lines 5766-5775: the reference program S21 (exact quadratic-field arithmetic,
capped integer operations), the ideal register IR S22 computing the same predicate on
every five-natural tuple, the all-input argument (normalized signed arithmetic, origin and
zero-ordinate cases, equal-abscissa addition, early rejections), nine polynomial identities
for the projective formulas, termination of the halving, division-by-four and factorial
loops.

## Section 10 threshold

Section 10, lines 5777-5781: for $\epsilon=U/V>0$ and $B\ge0$,
$4\epsilon<4^{-B}\iff4^B\le\lfloor(V-1)/(4U)\rfloor$.

## Section 10 saturation

Section 10, lines 5782-5788: $\sigma(x)=\min(x,L+1)$ for $L>0$ commutes with saturated
addition and multiplication; powers and factorials with saturation; capping exponents for
bases at least two; bases zero and one and exponent zero separately.

## Section 10.1 saved polynomial

Section 10.1, lines 5790-5795: the saved precision polynomial has $1\,305\,811$ natural
variables, the first five being inputs; its SHA-256.

## Section 10.1 wrapper specialization

Section 10.1, lines 5796-5805: S23 specializes a universal natural halting polynomial at the
code of a wrapper that inverts four Cantor pairs and then runs the precision machine; the
pairing equations $2t_i=(c_i+t_{i+1})(c_i+t_{i+1}+1)+2t_{i+1}$, $t_4=c_4$; unique unpairing;
the new polynomial is the square of the old one plus the four squared differences.

## Section 10.1 packed histories

Section 10.1, lines 5807-5824: acceptance (unique final halt, all registers zero, cleanup),
$c>0$, $K=2^c$, $B=4K>m$, $T=B^q$, $F_q=1+B+\dots+B^q$, $D=(K-1)F_q$, inputs below $K$,
masking, $R_j$ masked by $D$ with $R_j<T$, $S_i$ masked by $F_q$,
$\sum_iS_i=F_q$, $S_{\rm halt}=T$, and their digit consequences.

## Section 10.1 nonzero and branch masks

Section 10.1, lines 5826-5841: $KN_j=(R_j+D)\,\mathrm{AND}\,(KF_q)$ with the digit argument
$r+K-1<2K<B$; $V_i=S_i\,\mathrm{AND}\,N_j$, $S_i=V_i+W_i$; the indicators $A_j,C_j,I_i$
with zero-one digits.

## Section 10.1 transition equations

Section 10.1, lines 5841-5853: $R_j+BC_j=\mathrm{initial}_j+BR_j+BA_j$,
$S_i=\mathbf 1_{i=0}+BI_i$; coefficients at most $K<B$; uniqueness of base-$B$ digits; the
extra final slot; the case $q=0$; completeness for every finite accepting run.

## Section 10.2 alpha recurrence

Section 10.2, lines 5855-5878: the AFP sources (`Exp_Matrices.alpha_equations`,
`alpha_equivalence`, `Exponential_Relation.exp_repr`, `exp_dioph`); $U_n=\alpha_b(n)$;
growth for $b\ge3$; the matrix $M$ and $M^n$; determinant one, coprimality, the quadratic
identity; parameter congruence; $\alpha_2(n)=n$.

## Section 10.2 Pell classification

Section 10.2, lines 5880-5885: every natural solution of $x^2+y^2=1+bxy$, $b>2$, is an
unordered adjacent pair, by descent.

## Section 10.2 divisibility

Section 10.2, lines 5887-5896: $U_k\mid U_m\iff k\mid m$ for $k>0$, and equation (C.1):
$U_k^2\mid U_m\iff kU_k\mid m$ for $m>0$, including $k=0$.

## Section 10.2 period and reflection

Section 10.2, lines 5898-5905: $v=U_{m+1}-U_{m-1}=\operatorname{tr}(M^m)$, $M^{2m}\equiv-I$,
$U_n\equiv(-1)^l\varepsilon U_j\pmod v$ for $n=2lm+\varepsilon j$, and $v>2U_m$ for $b\ge4$.

## Section 10.2 alpha formula

Section 10.2, lines 5907-5922: the fifteen conditions (C.2) and the replacement of strict
inequality, divisibility and congruence by equations with fresh natural witnesses.

## Section 10.2 alpha soundness

Section 10.2, lines 5924-5932: from (C.2) to $X=U_N$.

## Section 10.2 alpha completeness

Section 10.2, lines 5934-5943: witnesses for $X=\alpha_b(N)$, including $N=X=0$.

## Section 10.2 power formula

Section 10.2, lines 5945-5960: the power formula (C.3) with its two special branches and
the proof that it expresses $P=Q^R$.

## Section 10.2 binomial and bits

Section 10.2, lines 5962-5975: the binomial digit equation, Lucas's criterion, disjointness
and the bitwise AND gadget.

## Section 10.3 numbering

Section 10.3, lines 5977-5982: the numbering $e+1=2^w(2D+1)$ and its total decoding.

## Section 10.3 interpreter

Section 10.3, lines 5984-5997: tape lists $\operatorname{cons}(h,t)=2^h(2t+1)$, register
update, reserved jump register, copies, aliased addition, division, one loop per decoded
instruction, cleanup, and equivalence of the all-zero halt with virtual halting.

## Section 10.3 precision IR

Section 10.3, lines 5999-6016: signed pairs, field pairs, norm zero, guarded divisions,
Jacobian formulas and branches, the fixed projective point, the loops and capped
arithmetic; the IR terminates and agrees with the predicate on all five natural inputs.

## Section 10.3 lowering

Section 10.3, lines 6018-6025: primitive lowering with fresh auxiliary registers,
saturating decrement, repeated addition, guarded division, loops; acceptance enters
cleanup, rejection a permanent self-loop.

## Section 10.3 unpairing and wrapper

Section 10.3, lines 6027-6034: unpairing by the remainder loop, four repetitions into
registers zero to four, fresh cleared scratch, relocation of the precision machine.

## Section 10.3 specialization

Section 10.3, lines 6036-6050: the specialization (program input fixed to the wrapper code,
old packed input to variable five, $i\mapsto i+7$ for $i\ge2$ and block starts, pairing
variables five to eight), equation (C.4), and the absence of height, restricted-converse
or rational-model premises.

## Section 10.4 power blocks

Section 10.4, lines 6078-6086: the precision parent has $54056$ explicit variables and
$15845$ disjoint private blocks of $79$ variables; no parent variable node accesses a
private coordinate.

## Section 12 literal constants

Section 12 (`sec:size`), subsection "Quantitative syntax bounds" (from line 6362), lines 6373-6376: the checked facts about the saved expression include that
the absolute values of all literal fixed constants are at most $T$; the program literal
$c_3$ is one of these constants.

## Appendix B sources

Appendix B (`app:sources`), lines 6636-6639: S21 `variable-shift-precision.py.txt` (exact
decision program), S22 `precision-register.js.txt` (ideal IR and lowering), S23
`specialize-precision.js.txt` (wrapper specialization), S24
`integer-halting-correctness-proof.txt` (natural compiler).

## Compiler specification

Project-authored: `construction/integer-compiler-spec.txt`, Sections 1-6: circuit and
formula conventions (equality as a difference, conjunction as a sum of squares,
disjunction as a product, strict inequality, divisibility and congruence gadgets), the
alpha and power macros, binomial and bit macros, register-machine semantics, packed
histories with the emitted equations $BF+1=F+BT$ and $D+F=KF$, soundness and
completeness.

## Halting correctness proof

Project-authored: `construction/integer-halting-correctness-proof.txt` (S24), Sections 1-6:
transcription of the AFP alpha and power systems, binomial and bit macros, the packed-machine
theorem for any fixed program, Boolean compilation and hierarchical substitution of the
power template with blocks of $79$ witnesses, correctness of the fixed interpreter
($1{,}399$ states, $204$ registers), and the binding to the saved polynomial
($1{,}305{,}804$ variables, $15{,}845$ calls, one $474$-node power template).

## Compiler source

Project-authored: `construction/integer-diophantine-compiler.js`: the classes and functions
`Builder` (methods `lt`, `divides`, `congruent`, `alpha`, `power`, `binomial`, `odd`,
`orthogonal`, `mask`, `bitAnd`, `polynomial`), `validateProgram`, `compileRegisterMachine`
and `runMachine`; `construction/verify-integer-compiler.js` holds its finite tests.

## Saved precision polynomial

Project-authored: `construction/precision-natural-polynomial.json` (cross-check only). Its
structure, read with a JSON parser: $54056$ explicit variables (inputs `code_0..code_4` at
$0..4$, `tuple_0..tuple_3` at $5..8$), $293620$ nodes ($10$ constants, $54056$ variable
nodes, $125327$ additions, $98382$ multiplications, $15845$ calls), $15845$ witness blocks of
length $79$, one power template with $3$ parameters, $79$ witnesses and $474$ nodes; node $0$
is the program literal ($3{,}181{,}317$ decimal digits); the first $293568$ nodes are the
universal halting circuit with variable $0$ replaced by that literal, variable $1$ by
variable $5$ and every other variable and block start shifted by $7$; the last $52$ nodes
form the four pairing equations and the final sum of squares. Decoding the literal with the
numbering gives $w=18$ and a primitive program of $146{,}779$ encoded states plus the
implicit final halt, using $23{,}633$ registers. The universal interpreter program
($1{,}399$ instructions: $1{,}022$ decrements, $376$ increments, the final halt; $204$
registers) is recovered from the variable names and state equations of the universal part,
and recompiling it with `compileRegisterMachine` in hierarchical mode reproduces those
$293568$ nodes exactly.

## AFP DPRM development

The Archive of Formal Proofs entry `DPRM_Theorem` (pinned in the halting correctness proof):
`Exponentiation.thy` (lines 1038 and 1690: `alpha_equivalence`), `Alpha_Sequence.thy`
(line 11: `alpha_dioph`), `Exponential_Relation.thy` (lines 9 and 16: `exp_repr`,
`exp_dioph`). External, read-only; not bundled in this repository.
