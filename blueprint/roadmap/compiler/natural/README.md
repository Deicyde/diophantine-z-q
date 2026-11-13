---
article_id: af_a59043516f48d09a2fae0c7c
---

# The natural precision polynomial

This chapter proves the natural half of input $\mathsf C$: an explicit polynomial
$[\![\mathcal N]\!]$ in $1{,}305{,}811$ variables, the first five being inputs, has a zero with
natural witnesses exactly at the five-tuples accepted by the exact precision computation
(equation (C.4) of the manuscript). Following the construction principle of the
formalization, $\mathcal N$ is not read from the saved file: it is *defined* as the output of a
compiler applied to explicit programs, and the saved file
`construction/precision-natural-polynomial.json` only cross-checks its shape.

The construction has three layers, and the chapter proves each separately.

1. *A generic compiler.* Any primitive register program is compiled into a natural
   circuit whose natural zeros are exactly its accepting inputs. Runs are packed into
   base-$B$ integers; the packing conditions are bit masks and exponentials; masks become
   binomial coefficients through Lucas's criterion; binomial coefficients become base-$B$
   digits of a power; and every power is one call of a fixed *power template*, the
   Matiyasevich-Robinson exponential relation of the Archive of Formal Proofs development
   written with the alpha sequence.
2. *Specific programs.* A universal interpreter, a wrapper that inverts four Cantor pairs,
   and a precision program written in an ideal register language and lowered to a
   primitive program; each is verified against its specification, the last against the
   mathematical precision relation.
3. *Counts.* The variable, gadget and node counts of the compiled circuits, needed by the
   witness accounting of the specification chapter.

The manuscript does not compile the precision machine directly. It compiles a fixed
universal interpreter ($1{,}399$ instructions, $204$ registers) once, and specializes the
resulting universal halting polynomial at the code of the wrapper. This is forced by the
variable budget: the interpreter costs $15{,}845$ power calls, whereas compiling the wrapper
itself ($146{,}780$ instructions, $23{,}633$ registers in the manuscript's version) would cost,
by the count $2+3(m+4r+3s)$ of the packed construction, at least
$2+3(146{,}780+4\cdot23{,}633)=723{,}938$ power calls even with no decrement instruction. The precision program enters the polynomial only through one integer
coefficient, the program literal $c_3$, which is never evaluated; neither are the
astronomically large constants $D$, $Q_0$ or $A^{(0)}_{\rm ht}$ of the precision computation,
which the program evaluates with caps.

## The exact precision computation

The precision relation decodes five naturals into $(n,\kappa,a,l,j)$, applies the early
tests, and compares two exact rational quantities built from the local parameter
$z=-x/y$ at multiples of $P_0$. The exact decision program computes it with integer pairs,
Jacobian coordinates and capped arithmetic.

- [The exact precision computation](precision/README.md)

## The alpha and power formulas

The power template rests on the alpha sequence $\alpha_b$, its Pell equation, divisibility
and period, the fifteen-condition alpha formula (C.2) and the power formula (C.3); the
binomial-digit equation and Lucas's criterion turn bit operations into powers.

- [The alpha and power formulas](exponential/README.md)

## Natural constructions and the power interface

The compiler's builder writes formulas with fresh natural witnesses; the macros mean what
they should; the power template is the compiled power macro; and a hierarchical
construction calls it on private blocks of $79$ variables.

- [Natural constructions and the power interface](formulas/README.md)

## The packed-history compiler

A finite run of a primitive program is packed into register and state histories; masks,
the nonzero indicator, branch histories and two families of transition equations
characterize accepting runs.

- [The packed-history compiler](packed/README.md)

## Programs, lowering and the wrapper

The ideal register language, its lowering to primitive programs, the precision program,
and the Cantor wrapper.

- [Programs, lowering and the wrapper](programs/README.md)

## The universal interpreter and the five-input circuit

The program numbering, the interpreter, the universal halting circuit, its specialization
at the wrapper code, and the node statistics.

- [The universal interpreter and the five-input circuit](universal/README.md)

## Equation (C.4)

The four reductions compose: the specialized circuit has a natural zero at $c$ iff the
halting circuit has one at $(c_3,\operatorname{enc}_5(c))$, iff the wrapper halts on
$\operatorname{enc}_5(c)$, iff $c$ is accepted.

- [Semantics of the natural precision polynomial](natural-polynomial-semantics.md)
