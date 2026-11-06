# Locators for the compiler-translation chapter

Line ranges refer to `diophantine_zq.tex` in this repository (the 11/5 manuscript, SHA-256
`cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`). TeX labels are given
where the item has one. Section 10 is `sec:compiler`; its subsections 10.3 and 10.4 carry
no labels. Project artifacts are listed last; they are cross-checks of the construction,
not inputs to the proof.

## Input C

Section 1, lines 102-104: input C of Lemma 1.2 (`lem:assembly`), "the actual five-input
natural polynomial and its rational translation have the exact computation and
substitution semantics of Section 10, including the power template". Lines 133-135 (proof
of Theorem 1.1, `thm:target`): Section 10 proves C; the witness variables remain natural
before the translation.

## Section 3.1 natural predicate

Section 3.1, lines 362-371: raw addition has the narrow contract on canonical codes; every
later use supplies canonical input codes; multiplication imposes membership of its three
roots and is sound on arbitrary rational tuples; in the natural predicate four initially
untyped tuples enter multiplication calls, so are typed before their squares are added;
Lagrange's theorem then gives exactly $\iota(\mathbb N)$; this uses multiplication
completeness.

## Section 4 height constants

Section 4 (`sec:height`), lines 381 and 385-399: the six-contact polynomial
$F(u)=u(u+15)(u+20)(u+24)(u+30)(u+60)$ (line 381); the constants $F_0$, $D$, $G_0$, $E_0$,
$Q_R$, $B_{\rm cm}$, $C_{\rm cm}$, $H_6(S;R)$ and the convention
$H_6(S)=H_6(S;\max(D,\max S,10^{12}))$ (line 399). Line 968: $S_{\rm ht}=\{p:p\le324\}$.

## Section 10 opening

Section 10 (`sec:compiler`), lines 5745-5789: the signed encoding
$\operatorname{enc}(n)=2n$ for $n\ge0$ and $-2n-1$ for $n<0$ (lines 5746-5749); the input
order $(n,\kappa,a,l,j)$ and the early rejections $n\notin\mathcal C$, $\kappa\ne0$,
$a,l\ge1$, $j=na$ (lines 5750-5751); $z=-x/y$, $z([l]P_0)=u_l+v_ls$,
$\epsilon_l=|u_l|+|v_l|$, $r(a,j)=\tfrac12\operatorname{Tr}(z([j]P_0)/z([a]P_0))$
(lines 5752-5757); $A^{(0)}_{\rm ht}=H_6(S_{\rm ht})$ and the two strict final tests
(lines 5758-5763); the reference program S21 and the ideal IR S22 with its all-input
argument (lines 5766-5775); the integer form $4\epsilon<4^{-B}\iff
4^B\le\lfloor(V-1)/(4U)\rfloor$ and the saturation $\sigma(x)=\min(x,L+1)$ (lines
5777-5788).

## Section 10.1 Cantor wrapper and acceptance

Section 10.1, lines 5790-5815: the saved precision polynomial has $1\,305\,811$ natural
variables, the first five inputs (lines 5791-5792); S23 specializes a universal natural
halting polynomial at the code of a wrapper that inverts four Cantor pairs (lines
5796-5798); the pairing equations
$2t_i=(c_i+t_{i+1})(c_i+t_{i+1}+1)+2t_{i+1}$ ($0\le i<4$), $t_4=c_4$, and the new
polynomial as the sum of the squared old polynomial and the four squared differences
(lines 5799-5804); acceptance of a fixed increment/decrement/branch program means reaching
the unique final halt with all registers zero, with a finite cleanup stage (lines
5807-5809).

## Section 10.3 program numbering

Section 10.3, lines 5977-5982: the universal numbering $e+1=2^w(2D+1)$; $w=0$ halts;
otherwise the four base-$2^w$ digits at positions $4p,\dots,4p+3$ give opcode, register and
two targets of state $p$; opcode one increments, opcode two decrements or takes its zero
branch, every other opcode halts; missing digits are zero, so decoding is total.

## Section 10.3 interpreter

Section 10.3, lines 5984-5997: the tape code $0$ or $\operatorname{cons}(h,t)=2^h(2t+1)$;
decoding by repeated halving, the tail smaller than the code; register update by saving the
reversed prefix; absent entries are zero; the reserved jump register stays zero; copies
restore their source; aliased addition snapshots its operand; division maintains
$x=qy+r$ and subtracts only when $r\ge y$, with divisors at least two; one interpreter loop
executes exactly one decoded instruction with finite work; a simulated halt enters cleanup;
an infinite simulation never does; the all-zero halt is equivalent to virtual halting.

## Section 10.3 precision IR

Section 10.3, lines 5999-6016: normalized signed pairs and pairs over $1,\sqrt2$; norm zero
implies zero (a primitive solution of $a^2=2b^2$ would have both entries even); every
division guarded by that test; the Jacobian formulas satisfy the curve equation and the
affine chord and tangent formulas after multiplying denominators; equal abscissas split
into doubling and opposite points; zero ordinate doubles to the identity; the fixed
projective point is $P_0$; these identities are independent of the generator theorem; the
scalar loop halves, the precision loop divides by four; capped arithmetic computes
$\min(x,L+1)$ with zero bases, unit bases and zero exponents separate; the ideal IR
terminates and agrees with the predicate on all five natural inputs.

## Section 10.3 lowering

Section 10.3, lines 6018-6025: each primitive lowering uses fresh auxiliary registers,
snapshots overlapping sources and preserves the live-register map at the end of each finite
block; saturating decrement gives natural subtraction; repeated addition gives
multiplication; variable divisions are guarded; induction on completed loop iterations
handles loops; acceptance enters cleanup, rejection a permanent self-loop; the primitive
machine halts exactly on acceptance.

## Section 10.3 unpairing wrapper

Section 10.3, lines 6027-6034: $\operatorname{pair}(a,b)=(a+b)(a+b+1)/2+b$; the unpairing
loop invariant $\text{remainder}=\text{input}-s(s+1)/2$, subtracting $s+1$ while
$s<\text{remainder}$; at exit $b=\text{remainder}$, $a=s-b$; four repetitions put the five
codes into registers zero to four; fresh scratch above the old register range, cleared;
relocation of every target by the prefix length.

## Section 10.3 specialization

Section 10.3, lines 6036-6050: the polynomial specialization fixes the universal program
input to the wrapper code, maps the old packed input to variable five and every old
variable $i\ge2$ and private-block start by $i\mapsto i+7$; the pairing variables occupy
five to eight; the four squared equations force the Cantor values; equation (C.4)
(lines 6042-6047); the natural compiler proof has no height, restricted-converse or
rational-model premise (lines 6048-6050).

## Section 10.4 typing order

Section 10.4, lines 6052-6076: the typing order (membership, raw addition on canonical
inputs, fixed scalars on $D$, the root membership conjuncts inside the height certificate,
the natural predicate only after globally typed multiplication, canonical outputs by the
raw-addition postcondition, generator equations outside internal products); induction on
the source DAG gives each node the code of its signed integer value; natural guards
constrain source variables, not intermediate sums or products; scalar templates supply
constants.

## Section 10.4 power value and precision parent

Section 10.4, lines 6078-6086: the power-value recipe (three signed code inputs,
seventy-nine private natural witnesses, an output code for the value of the
power-template polynomial, not required to vanish, root equality $[17751579,15]$); the
precision parent ($54056$ explicit variables, $15845$ disjoint private blocks of
seventy-nine variables, no parent variable node accessing a private coordinate);
replacing each block by its private power-value call preserves the existential
assignment; only the final parent root is equated to the identity.

## Section 10.4 primitive formulas

Section 10.4, lines 6088-6092: equality is a difference, conjunction a sum of squares,
disjunction a product; a topological induction including the globally conjoined fixed
equations proves equality of polynomial values under substitution.

## Section 11 precision contract

Section 11 (`sec:bridge`), lines 6103-6114 and 6236-6252: $\mathrm{Close}$ links the five
signed codes to the precision inputs in the order $(n,\kappa,a,l,j)$; the precision
contract is used with $B(n,\kappa)=H_6(S_{\rm ht})|\kappa F(n)|^{24}$.

## Section 12 literal constants

Section 12 (`sec:size`), lines 6372-6381: for the saved expression, the absolute values of all
literal fixed constants and all occurring division-polynomial indices are at most $T$; the
check covers the 173 scalar constant nodes. Appendix C (`app:literal`), lines 6778-6781: the
five scalar-constant templates use the values in `library.fixedConstants`, and large program
literals (the constant $c_3$) are retained byte for byte. The manuscript gives no explicit
bound on $c_3$; the bound $c_3<2^{2^{27}}$ is introduced in this chapter.

## Appendix C.2 model recipes

Appendix C.2, lines 6722-6730: a model-evaluation recipe sums the squares of the generator
equations, the natural calls, the scalar-constant calls, the add, multiply and power-value
calls and the five root differences; source-node and provenance fields add no equations.

## Lagrange four squares

Classical: every natural number is a sum of four squares of integers (Lagrange, 1770). Used
in Section 3.1, line 370, and Section 2.1, lines 190-197.

## Translation artifacts

Project artifacts (cross-checks only): `construction/rational-circuit-translator.js`
(class `Translator`, method `translate`: allocation order, point references, constant map,
operation records, root equality); `construction/audit-rational-expression.js`
(`auditEvaluation`: source-variable rows, constant provenance, operation operands, private
blocks, coverage); `construction/rational-model-assembly.js` (`addNaturalModel`: four
multiplication calls and three raw additions); `construction/ordinary-integer-polynomial.js`
(translation of the power template, then of the precision circuit; input order
`n_code, kappa_code, a_code, ell_code, j_code`); `construction/ordinary-integer-definition.json`
(`definitions.modelRecordEncoding`, `definitions.modelRecipeConstraints`,
`definitions.pointReferences`, `recipes.power_value`, `recipes.precision`);
`construction/precision-natural-polynomial.json` (SHA-256
`f3e163f5c60b972c98b48647274f956dd7d78428e27ddc0543574a5f18120b8c`; `metadata.codeNodes`,
`tupleNodes`, `pairingEquationNodes`, `programCodeNode`, the power template `templates[0]`
with meaning "Result=base^exponent on N").

## Machine artifacts

Project notes (historical scope, cross-checks only):
`construction/integer-compiler-spec.txt` section 4 (register-machine semantics: `add`,
`sub`, final halt, acceptance with all registers zero) and
`construction/integer-halting-correctness-proof.txt` section 5 (the numbering, the
primitive assembler macros `copy`, `addInto`, `ifLt`, `divmod`, `divmod2`, the tape
`cons`/`uncons`/`getList`/`setList`, the main-loop invariant, cleanup of all 204 registers,
the 1,399-state interpreter). The sources S21 (`variable-shift-precision.py`), S22
(`precision-register.js`), S23 (`specialize-precision.js`) and the universal interpreter
generator are listed in Appendix B (`app:sources`, lines 6636-6638) but are not in this repository.
